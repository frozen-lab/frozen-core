//! Implementation of on-disk bitmap

use crate::{
    error::FrozenRes,
    fmmap::{FMCfg, FrozenMMap},
};
use std::{sync::atomic, time};

/// Custom type `T` representing single `chunk` of bits on `FrozenFile`
///
/// Every chunk contains `64` bits
type T = u64;

const SLOT_FULL: u64 = T::MAX;
const BITS_PER_SLOT: usize = std::mem::size_of::<T>() * 8;

/// Config for [`FrozenBits`]
#[derive(Debug, Clone)]
pub struct FBCfg {
    /// Number of chunks to pre-allocated, where every chunk contains 64 bits
    pub initial_count: usize,

    /// Time interval used by background thread for batched flushing, which batches write ops into a durable window
    /// and sync them together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,
}

impl From<FBCfg> for FMCfg {
    fn from(value: FBCfg) -> Self {
        Self {
            initial_count: value.initial_count,
            flush_duration: value.flush_duration,
        }
    }
}

/// An os-disk bitmap implementation
#[derive(Debug)]
pub struct FrozenBits<const MODULE_ID: u8> {
    curr_idx: atomic::AtomicUsize,
    map: FrozenMMap<T, MODULE_ID>,
}

impl<const MODULE_ID: u8> FrozenBits<MODULE_ID> {
    /// Create a new instance of [`FrozenBits`]
    pub fn new<P: AsRef<std::path::Path>>(path: P, cfg: FBCfg) -> FrozenRes<Self> {
        let map: FrozenMMap<T, MODULE_ID> = FrozenMMap::new(path, cfg.into())?;

        Ok(Self {
            map,
            curr_idx: atomic::AtomicUsize::new(0),
        })
    }

    /// Allocate `N` free slots, where `N` is a muliple of 2
    #[inline(always)]
    pub fn allocate_2x(&self, n: usize) -> FrozenRes<Option<usize>> {
        let total = self.map.total_slots();
        let mut idx = self.curr_idx.load(atomic::Ordering::Acquire);

        while idx < total {
            let mut found = None;
            let _ = unsafe {
                self.map.write(idx, |slot| {
                    let val = *slot;

                    if val == SLOT_FULL {
                        return;
                    }

                    let free = !val;
                    let candidates = find_run(free, n);

                    if candidates == 0 {
                        return;
                    }

                    let bit = candidates.trailing_zeros() as usize;
                    let mask = ((1u64 << n) - 1) << bit;

                    // re-check (still needed inside closure)
                    if (val & mask) != 0 {
                        return;
                    }

                    *slot = val | mask;
                    found = Some(bit);
                })
            }?;

            if let Some(bit) = found {
                self.advance_cursor(idx);
                return Ok(Some(idx * BITS_PER_SLOT + bit));
            }

            idx += 1;
        }

        Ok(None)
    }

    #[inline(always)]
    fn advance_cursor(&self, new_idx: usize) {
        let mut current = self.curr_idx.load(atomic::Ordering::Relaxed);
        while new_idx > current {
            match self.curr_idx.compare_exchange_weak(
                current,
                new_idx,
                atomic::Ordering::Release,
                atomic::Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(val) => current = val,
            }
        }
    }
}

#[inline(always)]
fn find_run(word: u64, n: usize) -> u64 {
    let mut acc = word;

    // collapse runs
    for i in 1..n {
        acc &= word >> i;
    }

    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    const MID: u8 = 0;
    const FLUSH: time::Duration = time::Duration::from_micros(10);

    fn new_tmp(slots: usize) -> FrozenBits<MID> {
        let dir = tempfile::tempdir().expect("tmpdir");
        let path = dir.path().join("bitmap");

        let cfg = FBCfg {
            initial_count: slots,
            flush_duration: FLUSH,
        };

        FrozenBits::<MID>::new(path, cfg).expect("create bitmap")
    }

    mod twox_alloc_free {
        use super::*;

        #[test]
        fn ok_single_alloc() {
            let bits = new_tmp(1);

            let idx = bits.allocate_2x(2).expect("alloc").expect("some");
            assert_eq!(idx, 0);
        }

        #[test]
        fn ok_alloc_respects_occupied() {
            let bits = new_tmp(1);

            let idx = bits.allocate_2x(2).expect("alloc").expect("some");
            assert_eq!(idx, 0);

            let idx2 = bits.allocate_2x(2).expect("alloc").expect("some");
            assert_eq!(idx2, 2);
        }

        #[test]
        fn ok_fill_entire_slot() {
            let bits = new_tmp(1);

            for i in 0..0x20 {
                let idx = bits.allocate_2x(2).expect("alloc").expect("some");
                assert_eq!(idx, i * 2);
            }

            let none = bits.allocate_2x(2).expect("alloc");
            assert!(none.is_none());
        }

        #[test]
        fn ok_var_sizes() {
            let bits = new_tmp(1);

            let a = bits.allocate_2x(4).expect("alloc").unwrap();
            let b = bits.allocate_2x(2).expect("alloc").unwrap();
            let c = bits.allocate_2x(8).expect("alloc").unwrap();

            assert_eq!(a, 0);
            assert_eq!(b, 4);
            assert_eq!(c, 6);
        }

        #[test]
        fn ok_skip_used_regions() {
            let bits = new_tmp(1);

            let _ = bits.allocate_2x(4).expect("alloc");
            let _ = bits.allocate_2x(4).expect("alloc");

            // first 8 bits used
            let idx = bits.allocate_2x(2).expect("alloc").unwrap();
            assert_eq!(idx, 8);
        }

        #[test]
        fn ok_multi_slot_scan() {
            let bits = new_tmp(2);

            // fill first slot
            for _ in 0..0x20 {
                bits.allocate_2x(2).expect("alloc");
            }

            // should move to next slot
            let idx = bits.allocate_2x(2).expect("alloc").unwrap();
            assert_eq!(idx, 0x40);
        }

        #[test]
        fn ok_exact_fit() {
            let bits = new_tmp(1);

            let _ = bits.allocate_2x(0x3E).expect("alloc");
            let idx = bits.allocate_2x(2).expect("alloc").unwrap();

            assert_eq!(idx, 0x3E);

            let none = bits.allocate_2x(2).expect("alloc");
            assert!(none.is_none());
        }

        #[test]
        fn ok_concurrent_allocs() {
            let bits = Arc::new(new_tmp(2));

            let mut handles = vec![];
            for _ in 0..4 {
                let b = bits.clone();
                handles.push(thread::spawn(move || {
                    for _ in 0..0x10 {
                        let _ = b.allocate_2x(2).expect("alloc");
                    }
                }));
            }

            for h in handles {
                h.join().expect("join");
            }

            // ensure no panic + consistent usage
            let none = bits.allocate_2x(2).expect("alloc");
            assert!(none.is_none());
        }
    }
}
