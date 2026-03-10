//! NA

#![allow(unused)]

use crate::{
    bpool,
    error::{FrozenErr, FrozenRes},
    ffile, hints, mpscq,
};
use std::{
    sync::{self, atomic},
    thread, time,
};

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
    core: sync::Arc<Core>,
    tx: Option<thread::JoinHandle<()>>,
}

impl FrozenPipe {
    /// Create a new instance of [`FrozenPipe`]
    pub fn new(cfg: FPCfg) -> FrozenRes<Self> {
        let core = Core::new(cfg)?;
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self { core, tx: Some(tx) })
    }

    /// Submit a write request
    #[inline(always)]
    pub fn write(&self, buf: &[u8], index: usize) -> FrozenRes<u64> {
        let chunk_size = self.core.cfg.chunk_size;
        let chunks = (buf.len() + chunk_size - 1) / chunk_size;

        let _lock = self.core.acquire_io_lock()?;
        let alloc = self.core.pool.allocate(chunks)?;

        let mut src_off = 0usize;
        for ptr in alloc.slots() {
            if src_off >= buf.len() {
                break;
            }

            let remaining = buf.len() - src_off;
            let copy = remaining.min(chunk_size);

            unsafe { std::ptr::copy_nonoverlapping(buf.as_ptr().add(src_off), ptr.ptr, copy) };
            src_off += copy;
        }

        let req = WriteReq::new(index, chunks, alloc);
        self.core.mpscq.push(req);

        Ok(self.core.epoch.load(atomic::Ordering::Acquire))
    }

    /// Blocks until given `epoch` becomes durable
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        if let Some(sync_err) = self.core.get_sync_error() {
            return Err(sync_err);
        }

        let durable_epoch = self.core.epoch.load(atomic::Ordering::Acquire);
        if durable_epoch == 0 || durable_epoch > epoch {
            return Ok(());
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            // Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
            _ => panic!(),
        };

        loop {
            if let Some(sync_err) = self.core.get_sync_error() {
                return Err(sync_err);
            }

            if self.core.epoch.load(atomic::Ordering::Acquire) > epoch {
                return Ok(());
            }

            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                // Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
                _ => panic!(),
            };
        }
    }
}

impl Drop for FrozenPipe {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }
    }
}

#[derive(Debug)]
struct Core {
    cfg: FPCfg,
    cv: sync::Condvar,
    pool: bpool::BufPool,
    lock: sync::Mutex<()>,
    file: ffile::FrozenFile,
    epoch: atomic::AtomicU64,
    io_lock: sync::RwLock<()>,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    mpscq: mpscq::MPSCQueue<WriteReq>,
    error: atomic::AtomicPtr<FrozenErr>,
}

impl Core {
    fn new(cfg: FPCfg) -> FrozenRes<sync::Arc<Self>> {
        let file = ffile::FrozenFile::new(ffile::FFCfg {
            mid: cfg.mid,
            path: cfg.path.clone(),
            chunk_size: cfg.chunk_size,
            initial_chunk_amount: cfg.initial_chunk_amount,
        })?;
        let pool = bpool::BufPool::new(bpool::BPCfg {
            mid: cfg.mid,
            chunk_size: cfg.chunk_size,
            backend: bpool::BPBackend::Prealloc {
                capacity: cfg.pool_capacity,
            },
        });

        Ok(sync::Arc::new(Self {
            cfg,
            file,
            pool,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            epoch: atomic::AtomicU64::new(0),
            durable_cv: sync::Condvar::new(),
            mpscq: mpscq::MPSCQueue::default(),
            durable_lock: sync::Mutex::new(()),
            closed: atomic::AtomicBool::new(false),
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
        }))
    }

    #[inline]
    fn acquire_io_lock(&self) -> FrozenRes<sync::RwLockReadGuard<'_, ()>> {
        self.io_lock.read().map_err(|e| {
            // new_err_raw(FMMapErrRes::Lpn, e)
            panic!()
        })
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> FrozenRes<sync::RwLockWriteGuard<'_, ()>> {
        self.io_lock.write().map_err(|e| {
            // new_err_raw(FMMapErrRes::Lpn, e)
            panic!()
        })
    }

    #[inline]
    fn get_sync_error(&self) -> Option<FrozenErr> {
        let ptr = self.error.load(atomic::Ordering::Acquire);
        if hints::likely(ptr.is_null()) {
            return None;
        }

        Some(unsafe { (*ptr).clone() })
    }

    #[inline]
    fn set_sync_error(&self, err: FrozenErr) {
        let boxed = Box::into_raw(Box::new(err));
        let old = self.error.swap(boxed, atomic::Ordering::AcqRel);

        // NOTE: we must free the old error, if any, to avoid mem leaks
        if !old.is_null() {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn clear_sync_error(&self) {
        let old = self.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old.is_null()) {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn incr_epoch(&self) {
        self.epoch.fetch_add(1, atomic::Ordering::Release);
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<thread::JoinHandle<()>> {
        match thread::Builder::new()
            .name("fpipe-flush-tx".into())
            .spawn(move || Self::flush_tx(core))
        {
            Ok(tx) => Ok(tx),
            Err(error) => {
                let mut error = error.to_string().as_bytes().to_vec();
                error.extend_from_slice(b"Failed to spawn flush thread for FrozenMMap");
                panic!("{:?}", error); // NOTE: just a placeholder for now
            }
        }
    }

    fn flush_tx(core: sync::Arc<Self>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(error) => {
                let mut message = error.to_string().as_bytes().to_vec();
                message.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");
                // let error = FrozenErr::new(
                //     unsafe { MODULE_ID },
                //     ERRDOMAIN,
                //     FMMapErrRes::Lpn as u16,
                //     FMMapErrRes::Lpn.default_message(),
                //     message,
                // );
                // core.set_sync_error(error);
                return;
            }
        };

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.cfg.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    // core.set_sync_error(new_err_raw(FMMapErrRes::Txe, e));
                    return;
                }
            };

            // NOTE: we must read values of close brodcast before acquire exclusive lock,
            // if done otherwise, we impose serious deadlock sort of situation for the the flusher tx

            // we must close the thread when [`FrozenMMap`] is closed
            if hints::unlikely(core.closed.load(atomic::Ordering::Acquire)) {
                return;
            }

            // QUESTION: Should we drain after or before acquiring the exclusive lock
            let req_batch = core.mpscq.drain();
            if hints::unlikely(req_batch.len() == 0) {
                continue;
            }

            // INFO: we must acquire an exclusive IO lock for sync, hence no write, read or
            // grow could kick in while sync is in progress

            let io_lock = match core.acquire_exclusive_io_lock() {
                Ok(lock) => lock,
                Err(e) => {
                    // core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                    return;
                }
            };

            // INFO: we must drop the guard before syscall, as its a blocking operation and holding
            // the mutex while the syscall takes place is not a good idea, while we drop the mutex
            // and acqurie it again, in-between other process could acquire it and use it
            drop(guard);

            // NOTE:
            //
            // - if sync fails, we update the Core::error w/ the received error object
            // - we clear it up when another sync call succeeds
            // - this is valid, as the underlying sync flushes entire mmaped region, hence
            //   even if the last call failed, and the new one succeeded, we do get the durability
            //   guarenty for the old data as well

            match core.file.sync() {
                Ok(_) => {
                    core.incr_epoch();

                    let _g = match core.durable_lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            // core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                            return;
                        }
                    };

                    core.durable_cv.notify_all();
                    core.clear_sync_error();
                }
                Err(err) => core.set_sync_error(err),
            }

            drop(io_lock);
            guard = match core.lock.lock() {
                Ok(g) => g,
                Err(e) => {
                    // core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                    return;
                }
            };
        }
    }
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

#[derive(Debug)]
struct WriteReq {
    index: usize,
    chunks: usize,
    alloc: bpool::Allocation,
}

impl WriteReq {
    fn new(index: usize, chunks: usize, alloc: bpool::Allocation) -> Self {
        Self { index, chunks, alloc }
    }
}
