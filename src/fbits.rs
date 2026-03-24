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
