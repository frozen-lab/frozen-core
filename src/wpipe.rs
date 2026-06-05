#![allow(missing_docs)]
#![allow(unused)]

use crate::{
    bufpool,
    error::{FrozenError, FrozenResult},
    ffile, hints, mpscq,
};
use std::{ptr, sync, sync::atomic, thread, time};

/// All the available configurations for [`WritePipe`]
///
/// ## Example
///
/// ```
/// use frozen_core::wpipe::WritePipeCfg;
///
/// let cfg = WritePipeCfg {
///     module_id: 2,
///     flush_duration: std::time::Duration::from_millis(0x0A),
/// };
///
/// assert_ne!(cfg.module_id, 0);
/// assert_ne!(cfg.flush_duration.as_millis(), 0);
/// ```
#[derive(Debug, Clone)]
pub struct WritePipeCfg {
    /// Identifier used for error propagation by [`frozen_core::error::FrozenError`]
    pub module_id: u8,

    /// Time interval used by the background thread to perform hard sync for all the write
    /// operations submitted in the last durability window
    pub flush_duration: time::Duration,
}

#[derive(Debug)]
pub struct WritePipe {
    cfg: WritePipeCfg,
    core: sync::Arc<Core>,
    flush_tx_handle: Option<thread::JoinHandle<()>>,
}

unsafe impl Send for WritePipe {}
unsafe impl Sync for WritePipe {}

impl WritePipe {
    pub fn new(cfg: WritePipeCfg, file: sync::Arc<ffile::FrozenFile>) -> FrozenResult<Self> {
        Ok(Self { cfg, core: sync::Arc::new(Core::new(file)), flush_tx_handle: None })
    }

    #[inline]
    pub fn write(&self, req: WriteRequest) -> FrozenResult<u64> {
        let io_lock = self.core.acquire_shared_io_lock();
        if let Some(frozen_error) = self.core.get_flush_error() {
            return Err(frozen_error);
        }

        self.core.queue.push(req);
        Ok(self.core.increment_current_epoch())
    }
}

/// ## Why we ignore [`std::sync::PoisonError`]?
///
/// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not protect any mutable
/// state. All the pool invariants and accounting are maintained via atomics and are completely seperated from
/// the mutex.
///
/// A poisoned mutex only indicates that another tx panicked while holding the lock, and indicates an inconsistent
/// state of the protected value. Since no state can be left partially modified under this lock, there is no
/// possible consistency risk to recover from and propagating the poison error would only introduce unnecessary
/// failures into the allocation path.
///
/// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating with the recovered
/// guard.
fn bg_flush_thread(core: sync::Arc<Core>, flush_duration: time::Duration) {
    let mut guard = core.flush_guard.lock().unwrap_or_else(|e| e.into_inner());
    loop {
        (guard, _) = core.flush_cv.wait_timeout(guard, flush_duration).unwrap_or_else(|e| e.into_inner());

        let queued_ops = core.queue.drain();
        let closed = core.closed.load(atomic::Ordering::Acquire);

        if queued_ops.is_empty() {
            if closed {
                return;
            }

            continue;
        }

        let io_lock = core.acquire_exclusive_io_lock();

        let (min_index, max_index) = match core.write_queued_ops(queued_ops) {
            Ok(res) => res,
            Err(frozen_error) => {
                core.set_flush_error(frozen_error);
                drop(io_lock);

                continue;
            }
        };

        #[cfg(target_os = "linux")]
        if let Err(frozen_error) = core.file.sync_range(min_index, max_index - min_index) {
            core.set_flush_error(frozen_error);
            drop(io_lock);

            continue;
        }

        match core.file.sync() {
            Err(frozen_error) => {
                core.set_flush_error(frozen_error);
                drop(io_lock);

                continue;
            }
            Ok(_) => {
                core.mark_current_epoch_as_durable();
                core.del_flush_error();
            }
        }
    }
}

#[derive(Debug)]
struct Core {
    closed: atomic::AtomicBool,
    epoch: atomic::AtomicU64,
    durable_epoch: atomic::AtomicU64,
    file: sync::Arc<ffile::FrozenFile>,
    flush_cv: sync::Condvar,
    flush_error: atomic::AtomicPtr<FrozenError>,
    flush_guard: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    queue: mpscq::MPSCQueue<WriteRequest>,
}

unsafe impl Send for Core {}

impl Core {
    fn new(file: sync::Arc<ffile::FrozenFile>) -> Self {
        Self {
            file,
            closed: atomic::AtomicBool::new(false),
            epoch: atomic::AtomicU64::new(0),
            durable_epoch: atomic::AtomicU64::new(0),
            flush_cv: sync::Condvar::new(),
            flush_error: atomic::AtomicPtr::new(ptr::null_mut()),
            flush_guard: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            queue: mpscq::MPSCQueue::default(),
        }
    }

    #[inline]
    fn set_flush_error(&self, new_error: FrozenError) {
        let boxed_err = Box::into_raw(Box::new(new_error));
        let old_err = self.flush_error.swap(boxed_err, atomic::Ordering::AcqRel);

        if hints::unlikely(!old_err.is_null()) {
            unsafe {
                drop(Box::from_raw(old_err));
            }
        }
    }

    #[inline]
    fn get_flush_error(&self) -> Option<FrozenError> {
        let error_ptr = self.flush_error.load(atomic::Ordering::Acquire);
        if hints::likely(error_ptr.is_null()) {
            return None;
        }

        let frozen_error = unsafe { (*error_ptr).clone() };
        Some(frozen_error)
    }

    #[inline]
    fn del_flush_error(&self) {
        let old_error = self.flush_error.swap(ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old_error.is_null()) {
            unsafe {
                drop(Box::from_raw(old_error));
            }
        }
    }

    #[inline]
    fn acquire_shared_io_lock(&self) -> sync::RwLockReadGuard<'_, ()> {
        // NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
        self.io_lock.read().unwrap_or_else(|e| e.into_inner())
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> sync::RwLockWriteGuard<'_, ()> {
        // NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
        self.io_lock.write().unwrap_or_else(|e| e.into_inner())
    }

    #[inline(always)]
    fn write_queued_ops(&self, queued_ops: Vec<WriteRequest>) -> FrozenResult<(usize, usize)> {
        let mut min_index = 0;
        let mut max_index = usize::MAX;

        for op in queued_ops {
            match op.allocation.length() {
                1 => {
                    self.file.pwrite(op.allocation.first(), op.slot_index)?;
                }
                _ => {
                    let bufs: Vec<bufpool::BufferPointer> = op.allocation.iter().collect();
                    self.file.pwritev(&bufs, op.slot_index)?;
                }
            }
        }

        Ok((min_index, max_index))
    }

    #[inline]
    fn increment_current_epoch(&self) -> u64 {
        self.epoch.fetch_add(1, atomic::Ordering::Acquire)
    }

    #[inline]
    fn mark_current_epoch_as_durable(&self) {
        let curr_epoch = self.epoch.load(atomic::Ordering::Acquire);
        let _ = self.durable_epoch.swap(curr_epoch - 1, atomic::Ordering::AcqRel);
    }
}

#[derive(Debug)]
pub struct WriteRequest {
    slot_index: usize,
    allocation: bufpool::BufPoolAllocation,
}
