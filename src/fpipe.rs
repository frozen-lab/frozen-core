//! NA

#![allow(unused)]

use crate::{bpool, error::FrozenRes, ffile, mpscq};
use std::{sync::atomic, time};

/// Config for [`FrozenPipe`]
#[derive(Debug, Clone)]
pub struct FPCfg {
    /// Module id used for error logging
    pub mid: u8,

    /// Path for the file
    ///
    /// *NOTE:* The caller must make sure that the parent directory exists
    pub path: std::path::PathBuf,

    /// Size (in bytes) of a single chunk on fs
    ///
    /// A chunk is a smalled fixed size allocation and addressing unit used by [`FrozenFile`] for all the
    /// write/read ops, which are operated by index of the chunk and not the offset of the byte
    pub chunk_size: usize,

    /// Number of chunks to pin in-mem for [`BPool`], used by all write ops
    ///
    /// TODO: Add explanation
    pub pool_capacity: usize,

    /// Number of chunks to pre-allocate when [`FrozenFile`] is initialized
    ///
    /// Initial file length will be `chunk_size * initial_chunk_amount` (bytes)
    pub initial_chunk_amount: usize,

    /// Time interval used by flusher tx, to batch write ops into a durable window and sync them
    /// together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,
}

/// NA
#[derive(Debug)]
pub struct FrozenPipe {
    cfg: FPCfg,
    pool: bpool::BPool,
    file: ffile::FrozenFile,
    mpscq: mpscq::MPSCQueue<WriteReq>,
    epoch: atomic::AtomicUsize,
    closed: atomic::AtomicBool,
}

impl FrozenPipe {
    /// NA
    pub fn new(cfg: FPCfg) -> FrozenRes<Self> {
        let file = ffile::FrozenFile::new(Self::prep_ff_cfg(&cfg))?;
        let pool = bpool::BPool::new(cfg.chunk_size, cfg.pool_capacity, cfg.mid);

        Ok(Self {
            cfg,
            pool,
            file,
            epoch: atomic::AtomicUsize::new(0),
            mpscq: mpscq::MPSCQueue::default(),
            closed: atomic::AtomicBool::new(false),
        })
    }

    /// NA
    #[inline(always)]
    pub fn write(&self, bufs: &[u8], index: usize) {}

    fn prep_ff_cfg(cfg: &FPCfg) -> ffile::FFCfg {
        ffile::FFCfg {
            mid: cfg.mid,
            path: cfg.path.clone(),
            chunk_size: cfg.chunk_size,
            initial_chunk_amount: cfg.initial_chunk_amount,
        }
    }
}

impl Drop for FrozenPipe {
    fn drop(&mut self) {
        self.closed.store(true, atomic::Ordering::Release);
    }
}

#[derive(Debug)]
struct WriteReq {
    index: usize,
    alloc: bpool::Allocation,
}
