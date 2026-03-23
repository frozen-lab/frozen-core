//! Implementation of on-disk bitmap

use crate::{
    error::FrozenRes,
    fmmap::{FMCfg, FrozenMMap},
};
use std::{
    sync::{self, atomic},
    time,
};

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
    slots: atomic::AtomicUsize,
    curr_idx: atomic::AtomicUsize,
    map: FrozenMMap<T, MODULE_ID>,
}

impl<const MODULE_ID: u8> FrozenBits<MODULE_ID> {
    /// Create a new instance of [`FrozenBits`]
    pub fn new<P: AsRef<std::path::Path>>(path: P, cfg: FBCfg) -> FrozenRes<Self> {
        let slots = atomic::AtomicUsize::new(cfg.initial_count);
        let map: FrozenMMap<T, MODULE_ID> = FrozenMMap::new(path, cfg.into())?;

        Ok(Self {
            map,
            slots,
            curr_idx: atomic::AtomicUsize::new(0),
        })
    }

    /// Allocate `N` free slots, where `N` is a muliple of 2
    #[inline(always)]
    pub fn allocate_2x(&self, n: usize) -> FrozenRes<Option<usize>> {
        let curr_idx = self.curr_idx.load(atomic::Ordering::Acquire);
        let _epoch = unsafe {
            self.map.write(curr_idx, |slot| {
                if *slot == SLOT_FULL {
                    return;
                }
            })
        }?;

        Ok(Some(curr_idx * BITS_PER_SLOT))
    }
}
