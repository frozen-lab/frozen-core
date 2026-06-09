#![allow(missing_docs)]
#![allow(unused)]

use crate::{
    bufpool,
    error::{FrozenError, FrozenResult},
    ffile, hints, mpscq,
};
use std::{
    ptr,
    sync::{self, atomic},
    thread, time,
};

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
        let core = sync::Arc::new(Core::new(file));
        let cloned_core = core.clone();
        let flush_tx_handle = match thread::Builder::new()
            .name("wpipe_flush_tx".into())
            .spawn(move || bg_flush_thread(cloned_core, cfg.flush_duration))
        {
            Ok(handle) => Some(handle),
            Err(observed_error) => return Err(err::new_error(cfg.module_id, err::FXE, observed_error)),
        };

        Ok(Self { cfg, core: core, flush_tx_handle })
    }

    #[inline]
    pub fn write(&self, request: WriteRequest) -> FrozenResult<WriteTicket> {
        let _io_lock = self.core.acquire_shared_io_lock();
        if let Some(frozen_error) = self.core.completion.error.get() {
            return Err(frozen_error);
        }

        let epoch = self.core.increment_current_epoch();
        let internal_req = WriteRequestInternal { request, epoch };
        self.core.queue.push(internal_req);

        Ok(WriteTicket { epoch, completion: self.core.completion.clone() })
    }
}

impl Drop for WritePipe {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.flush_cv.notify_one();

        if let Some(handle) = self.flush_tx_handle.take() {
            let _ = handle.join();
        }
    }
}

#[derive(Debug)]
pub struct WriteRequest {
    allocation: bufpool::BufPoolAllocation,
    slot_index: usize,
}

#[derive(Debug)]
pub struct WriteTicket {
    epoch: u64,
    completion: sync::Arc<Completion>,
}

impl WriteTicket {
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    #[inline]
    fn is_ready(&self) -> bool {
        let durable = self.completion.durable_epoch.load(atomic::Ordering::Acquire);
        if hints::likely(durable >= self.epoch) {
            return true;
        }

        false
    }
}

impl std::future::Future for WriteTicket {
    type Output = FrozenResult<u64>;

    #[inline(always)]
    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
        if self.is_ready() {
            return std::task::Poll::Ready(Ok(self.epoch));
        }

        if let Some(frozen_error) = self.completion.error.get() {
            return std::task::Poll::Ready(Err(frozen_error));
        }

        self.completion.waker.register(cx.waker());

        if self.is_ready() {
            return std::task::Poll::Ready(Ok(self.epoch));
        }

        if let Some(frozen_error) = self.completion.error.get() {
            return std::task::Poll::Ready(Err(frozen_error));
        }

        std::task::Poll::Pending
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

        let _io_lock = core.acquire_exclusive_io_lock();
        let (min_index, max_index, max_epoch) = match core.write_queued_ops(queued_ops) {
            Ok(res) => res,
            Err(new_error) => {
                core.completion.error.set(new_error);
                core.completion.waker.wake();
                drop(_io_lock);

                continue;
            }
        };

        #[cfg(target_os = "linux")]
        if let Err(new_error) = core.file.sync_range(min_index, max_index - min_index) {
            core.completion.error.set(new_error);
            core.completion.waker.wake();
            drop(_io_lock);

            continue;
        }

        if let Err(new_error) = core.file.sync() {
            core.completion.error.set(new_error);
            core.completion.waker.wake();
            drop(_io_lock);

            continue;
        } else {
            core.completion.mark_epoch_as_durable(max_epoch);
            core.completion.error.del();
        }
    }
}

#[derive(Debug)]
struct Core {
    completion: sync::Arc<Completion>,
    closed: atomic::AtomicBool,
    epoch: atomic::AtomicU64,
    file: sync::Arc<ffile::FrozenFile>,
    flush_cv: sync::Condvar,
    flush_guard: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    queue: mpscq::MPSCQueue<WriteRequestInternal>,
}

impl Core {
    fn new(file: sync::Arc<ffile::FrozenFile>) -> Self {
        Self {
            file,
            completion: sync::Arc::new(Completion::default()),
            closed: atomic::AtomicBool::new(false),
            epoch: atomic::AtomicU64::new(0),
            flush_cv: sync::Condvar::new(),
            flush_guard: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            queue: mpscq::MPSCQueue::default(),
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
    fn write_queued_ops(&self, queued_ops: Vec<WriteRequestInternal>) -> FrozenResult<(usize, usize, u64)> {
        let mut max_epoch = 0;
        let mut max_index = 0;
        let mut min_index = usize::MAX;

        for op in queued_ops {
            let ops_len = op.request.allocation.length();
            match ops_len {
                1 => {
                    self.file.pwrite(op.request.allocation.first(), op.request.slot_index)?;
                }
                _ => {
                    let bufs: Vec<bufpool::BufferPointer> = op.request.allocation.iter().collect();
                    self.file.pwritev(&bufs, op.request.slot_index)?;
                }
            }

            max_epoch = max_epoch.max(op.epoch);
            min_index = min_index.min(op.request.slot_index);
            max_index = max_index.max(op.request.slot_index + ops_len);
        }

        Ok((min_index, max_index, max_epoch))
    }

    #[inline]
    fn increment_current_epoch(&self) -> u64 {
        self.epoch.fetch_add(1, atomic::Ordering::AcqRel).wrapping_add(1)
    }
}

#[derive(Debug)]
struct WriteRequestInternal {
    epoch: u64,
    request: WriteRequest,
}

#[derive(Debug)]
struct Completion {
    durable_epoch: atomic::AtomicU64,
    error: FlushError,
    waker: futures::task::AtomicWaker,
}

impl Default for Completion {
    fn default() -> Self {
        Self {
            durable_epoch: atomic::AtomicU64::new(0),
            waker: futures::task::AtomicWaker::new(),
            error: FlushError::default(),
        }
    }
}

impl Completion {
    fn mark_epoch_as_durable(&self, epoch: u64) {
        self.durable_epoch.store(epoch, atomic::Ordering::Release);
        self.waker.wake();
    }
}

#[derive(Debug)]
struct FlushError(atomic::AtomicPtr<FrozenError>);

impl Default for FlushError {
    fn default() -> Self {
        Self(atomic::AtomicPtr::new(ptr::null_mut()))
    }
}

impl Drop for FlushError {
    fn drop(&mut self) {
        let err_ptr = self.0.load(atomic::Ordering::Acquire);
        if !err_ptr.is_null() {
            let _ = unsafe { Box::from_raw(err_ptr) };
        }
    }
}

impl FlushError {
    #[inline]
    fn get(&self) -> Option<FrozenError> {
        let curr_err = self.0.load(atomic::Ordering::Acquire);
        if hints::unlikely(!curr_err.is_null()) {
            let frozen_error = unsafe { (*curr_err).clone() };
            return Some(frozen_error);
        }

        None
    }

    #[inline]
    fn set(&self, new_error: FrozenError) {
        let boxed_error = Box::into_raw(Box::new(new_error));
        let old_err = self.0.swap(boxed_error, atomic::Ordering::AcqRel);

        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }

    #[inline]
    fn del(&self) {
        let old_err = self.0.swap(ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }
}

mod err {
    use crate::error::{ErrCode, FrozenError};

    /// Domain ID for [`wpipe`] module is `0x02` used while propagating errors
    const DOMAIN_ID: u8 = 0x02;

    #[inline]
    pub fn new_error<E: std::fmt::Display>(module_id: u8, code: ErrCode, observed_error: E) -> FrozenError {
        FrozenError::new_raw(module_id, DOMAIN_ID, code, observed_error)
    }

    pub const FXE: ErrCode = ErrCode::new(0x10, "unable to spawn background flush thread");
}
