//! NA

use crate::{
    bpool,
    error::{FrozenErr, FrozenRes},
    ffile, hints, mpscq,
};
use std::{
    sync::{self, atomic},
    thread, time,
};

/// module id used for [`FrozenPipe`]
static mut MODULE_ID: u8 = 0;

/// Domain Id for [`FrozenPipe`] is **19**
const ERRDOMAIN: u8 = 0x13;

/// Error codes for [`FrozenPipe`]
#[repr(u16)]
pub enum FPError {
    /// (1024) internal fuck up (hault and catch fire)
    Hcf = 0x400,

    /// (1025) thread error or panic inside thread
    Txe = 0x401,

    /// (1026) lock error (failed or poisoned)
    Lpn = 0x402,
}

impl FPError {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned",
            Self::Hcf => b"hault and catch fire",
            Self::Txe => b"thread failed or paniced",
        }
    }
}

#[inline]
fn new_err<R>(res: FPError, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(unsafe { MODULE_ID }, ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
fn new_err_raw<E: std::fmt::Display>(res: FPError, error: E) -> FrozenErr {
    let detail = res.default_message();
    FrozenErr::new(
        unsafe { MODULE_ID },
        ERRDOMAIN,
        res as u16,
        detail,
        error.to_string().as_bytes().to_vec(),
    )
}

/// NA
#[derive(Debug)]
pub struct FrozenPipe {
    core: sync::Arc<Core>,
    tx: Option<thread::JoinHandle<()>>,
}

impl FrozenPipe {
    /// Create a new instance of [`FrozenPipe`]
    pub fn new(file: ffile::FrozenFile, pool: bpool::BufPool, flush_duration: time::Duration) -> FrozenRes<Self> {
        let core = Core::new(file, pool, flush_duration)?;
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self { core, tx: Some(tx) })
    }

    /// Submit a write request
    #[inline(always)]
    pub fn write(&self, buf: &[u8], index: usize) -> FrozenRes<u64> {
        let chunk_size = self.core.chunk_size;
        let chunks = buf.len().div_ceil(chunk_size);

        let alloc = self.core.pool.allocate(chunks)?;

        // NOTE: Read lock prevents torn syncs by ensuring the flusher_tx cannot acquire an exclusive lock unitl the
        // write ops is submited, while this lock must be acquired after pool allocations as `BufPool::allocate` may
        // block while waiting for chunks, otherwise the wait would delay the flusher from obtaining the lock, and
        // potentially stalling the durability progress for the entire `FrozenPipe`
        let _lock = self.core.acquire_io_lock()?;

        let mut src_off = 0usize;
        for ptr in alloc.slots() {
            if src_off >= buf.len() {
                break;
            }

            let remaining = buf.len() - src_off;
            let copy = remaining.min(chunk_size);

            unsafe { std::ptr::copy_nonoverlapping(buf.as_ptr().add(src_off), *ptr, copy) };
            src_off += copy;
        }

        let req = WriteReq::new(index, chunks, alloc);
        self.core.mpscq.push(req);

        Ok(self.core.epoch.load(atomic::Ordering::Acquire))
    }

    /// Blocks until given `epoch` becomes durable
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        self.internal_wait(epoch)
    }

    /// Force instant durability for the current batch
    pub fn force_durability(&self, epoch: u64) -> FrozenRes<()> {
        let guard = self.core.lock.lock().map_err(|e| new_err_raw(FPError::Lpn, e))?;
        self.core.cv.notify_one();
        drop(guard);

        self.internal_wait(epoch)
    }

    fn internal_wait(&self, epoch: u64) -> FrozenRes<()> {
        if hints::unlikely(self.core.epoch.load(atomic::Ordering::Acquire) > epoch) {
            return Ok(());
        }

        if let Some(sync_err) = self.core.get_sync_error() {
            return Err(sync_err);
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return Err(new_err_raw(FPError::Lpn, e)),
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
                Err(e) => return Err(new_err_raw(FPError::Lpn, e)),
            };
        }
    }
}

impl Drop for FrozenPipe {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.cv.notify_one(); // notify flusher tx to shut

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        // INFO: we must acquire an exclusive lock, to prevent dropping while sync,
        // growing or any read/write ops
        let _io_lock = self.core.acquire_exclusive_io_lock();

        // free up the boxed error (if any)
        let ptr = self.core.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }
    }
}

#[derive(Debug)]
struct Core {
    chunk_size: usize,
    cv: sync::Condvar,
    pool: bpool::BufPool,
    lock: sync::Mutex<()>,
    file: ffile::FrozenFile,
    epoch: atomic::AtomicU64,
    io_lock: sync::RwLock<()>,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    flush_duration: time::Duration,
    mpscq: mpscq::MPSCQueue<WriteReq>,
    error: atomic::AtomicPtr<FrozenErr>,
}

impl Core {
    fn new(
        file: ffile::FrozenFile,
        pool: bpool::BufPool,
        flush_duration: time::Duration,
    ) -> FrozenRes<sync::Arc<Self>> {
        let cfg = file.cfg();
        let chunk_size = cfg.chunk_size;

        // NOTE: we only set it the module_id once, hence it'll be only set once per instance
        // and is only used for error logging
        unsafe { MODULE_ID = cfg.mid };

        Ok(sync::Arc::new(Self {
            file,
            pool,
            chunk_size,
            flush_duration,
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
        self.io_lock.read().map_err(|e| new_err_raw(FPError::Lpn, e))
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> FrozenRes<sync::RwLockWriteGuard<'_, ()>> {
        self.io_lock.write().map_err(|e| new_err_raw(FPError::Lpn, e))
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

    fn write_batch(&self, batch: Vec<WriteReq>) -> FrozenRes<(usize, usize)> {
        let mut max_index = 0usize;
        let mut min_index = usize::MAX;

        for req in &batch {
            let slots = req.alloc.slots();
            match req.chunks {
                1 => {
                    self.file.pwrite(slots[0], req.index)?;
                }
                _ => {
                    self.file.pwritev(slots, req.index)?;
                }
            }

            min_index = min_index.min(req.index);
            max_index = max_index.max(req.index + req.chunks);
        }

        Ok((min_index, max_index))
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<thread::JoinHandle<()>> {
        match thread::Builder::new()
            .name("fpipe-flush-tx".into())
            .spawn(move || Self::flush_tx(core))
        {
            Ok(tx) => Ok(tx),
            Err(error) => {
                let mut error = error.to_string().as_bytes().to_vec();
                error.extend_from_slice(b"Failed to spawn flush thread for FrozenPipe");
                new_err(FPError::Hcf, error)
            }
        }
    }

    fn flush_tx(core: sync::Arc<Self>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(error) => {
                let mut message = error.to_string().as_bytes().to_vec();
                message.extend_from_slice(b"Flush thread died before init could be completed for FrozenPipe");
                let error = FrozenErr::new(
                    unsafe { MODULE_ID },
                    ERRDOMAIN,
                    FPError::Lpn as u16,
                    FPError::Lpn.default_message(),
                    message,
                );
                core.set_sync_error(error);
                return;
            }
        };

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FPError::Txe, e));
                    return;
                }
            };

            // INFO: we must drop the guard before syscall, as its a blocking operation and holding
            // the mutex while the syscall takes place is not a good idea, while we drop the mutex
            // and acqurie it again, in-between other process could acquire it and use it
            drop(guard);

            // NOTE: we must read values of close brodcast before acquire exclusive lock,
            // if done otherwise, we impose serious deadlock sort of situation for the the flusher tx

            let req_batch = core.mpscq.drain();
            let closing = core.closed.load(atomic::Ordering::Acquire);

            if req_batch.is_empty() {
                if closing {
                    return;
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        core.set_sync_error(new_err_raw(FPError::Lpn, e));
                        return;
                    }
                };

                continue;
            }

            // INFO: we must acquire an exclusive IO lock for sync, hence no write/read ops are allowed
            // while sync is in progress

            let io_lock = match core.acquire_exclusive_io_lock() {
                Ok(lock) => lock,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FPError::Lpn, e));
                    return;
                }
            };

            let (_min, _max) = match core.write_batch(req_batch) {
                Ok(res) => res,
                Err(err) => {
                    core.set_sync_error(err);
                    drop(io_lock);

                    guard = match core.lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(FPError::Lpn, e));
                            return;
                        }
                    };

                    continue;
                }
            };

            // NOTE:
            //
            // - if sync fails, we update the Core::error w/ the received error object
            // - we clear it up when another sync call succeeds
            // - this is valid, as the underlying sync flushes entire mmaped region, hence
            //   even if the last call failed, and the new one succeeded, we do get the durability
            //   guarenty for the old data as well

            match core.file.sync() {
                Err(err) => core.set_sync_error(err),
                Ok(()) => {
                    core.incr_epoch();
                    let _g = match core.durable_lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(FPError::Lpn, e));
                            return;
                        }
                    };

                    core.durable_cv.notify_all();
                    core.clear_sync_error();
                }
            }

            drop(io_lock);
            guard = match core.lock.lock() {
                Ok(g) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FPError::Lpn, e));
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
        Self { alloc, index, chunks }
    }
}
