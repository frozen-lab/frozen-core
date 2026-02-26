//! Custom implementation of `memmap`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{FrozenErr, FrozenRes},
    ffile::{FFCfg, FrozenFile},
    hints,
};
use std::{
    cell, fmt, mem,
    sync::{self, atomic},
    thread, time,
};

/// type for `epoch` used by write ops
type TEpoch = u64;

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenErr`]
static mut MODULE_ID: u8 = 0;

/// Error codes for [`FrozenFile`]
#[repr(u16)]
pub enum FMMapErrRes {
    /// (512) internal fuck up (hault and catch fire)
    Hcf = 0x200,

    /// (513) unknown error (fallback)
    Unk = 0x201,

    /// (514) no more memory available
    Nmm = 0x202,

    /// (515) syncing error
    Syn = 0x203,

    /// (516) thread error or panic inside thread
    Txe = 0x204,

    /// (517) lock error (failed or poisoned)
    Lpn = 0x205,

    /// (518) perm error (read or write)
    Prm = 0x208,
}

impl FMMapErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned",
            Self::Unk => b"unknown error type",
            Self::Nmm => b"no more memory left",
            Self::Hcf => b"hault and catch fire",
            Self::Prm => b"no perm to read or write",
            Self::Txe => b"thread failed or paniced",
            Self::Syn => b"failed to sync/flush data to storage device",
        }
    }
}

#[inline]
pub(in crate::fmmap) fn new_err<R>(res: FMMapErrRes, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(unsafe { MODULE_ID }, ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
pub(in crate::fmmap) fn new_err_raw<E: std::fmt::Display>(res: FMMapErrRes, error: E) -> FrozenErr {
    let detail = res.default_message();
    FrozenErr::new(
        unsafe { MODULE_ID },
        ERRDOMAIN,
        res as u16,
        detail,
        error.to_string().as_bytes().to_vec(),
    )
}

/// Custom implementation of MemMap
#[derive(Debug)]
pub struct FrozenMMap<T>
where
    T: Clone + Sized + Send + Sync,
{
    core: sync::Arc<Core>,
    _type: core::marker::PhantomData<T>,
}

unsafe impl<T> Send for FrozenMMap<T> where T: Clone + Sized + Send + Sync {}
unsafe impl<T> Sync for FrozenMMap<T> where T: Clone + Sized + Send + Sync {}

impl<T> FrozenMMap<T>
where
    T: Clone + Sized + Send + Sync,
{
    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.core.curr_length()
    }

    /// Create a new [`FrozenMMap`] for given `fd` w/ read/write perm
    pub fn new(cfg: FFCfg, flush_duration: time::Duration) -> FrozenRes<Self> {
        // NOTE: we only set it once, as once after an exclusive lock for the entire file is
        // acquired, hence it'll be only set once per instance and is only used for error logging
        unsafe { MODULE_ID = cfg.mid };

        let file = FrozenFile::new(cfg)?;
        let curr_length = file.length()?;

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, flush_duration, curr_length));

        // INFO: we spawn the thread for background sync
        Core::spawn_tx(core.clone())?;
        Ok(Self {
            core,
            _type: core::marker::PhantomData,
        })
    }

    /// Returns the [`FrozenErr`] representing the last error occurred in [`FrozenMMap`]
    #[inline]
    pub fn last_error(&self) -> Option<FrozenErr> {
        self.core.get_sync_error()
    }

    /// Wait for durability for the given write `epoch`
    ///
    /// This functions blocks until epoch becomes durable
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        if self.core.durable_epoch.load(atomic::Ordering::Acquire) >= epoch {
            return Ok(());
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
        };

        while self.core.durable_epoch.load(atomic::Ordering::Acquire) < epoch {
            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
            }
        }

        Ok(())
    }

    /// Get's a read only typed pointer for `T`
    #[inline]
    pub fn read<R>(&self, offset: usize, f: impl FnOnce(&T) -> R) -> FrozenRes<R> {
        let guard = self.core.acquire_guard()?;
        let ptr = unsafe { self.get_mmap().get(offset) };
        let res = unsafe { f(&*ptr) };

        drop(guard);
        Ok(res)
    }

    /// Get's a mutable typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, offset: usize, f: impl FnOnce(&mut T) -> R) -> FrozenRes<(R, TEpoch)> {
        let guard = self.core.acquire_guard()?;
        let mut val = unsafe { self.get_mmap().get_mut::<T>(offset).read() };
        let res = f(&mut val);

        let epoch = self.core.write_epoch.fetch_add(1, atomic::Ordering::AcqRel) + 1;
        self.core.dirty.store(true, atomic::Ordering::Release);

        drop(guard);
        Ok((res, epoch))
    }

    /// grow [`FrozenMMap`] by given `len_to_add`, by growing underlying [`FrozenFile`]
    /// and re-mapping on the grown region
    pub fn grow(&self, len_to_add: usize) -> FrozenRes<()> {
        let core = &self.core;

        // WARN: we must always acquire the mutext before starting grow
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
        };

        // pause all ops
        core.growing.store(true, atomic::Ordering::Release);

        // we must wait until all [`ActiveGuard`] instances are dropped
        while core.active.load(atomic::Ordering::Acquire) != 0 {
            guard = match core.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(FMMapErrRes::Txe, e.to_string().as_bytes().to_vec()),
            };
        }

        // swap dirty flag and manual sync to avoid any kind of data loss before unmap
        if core.dirty.swap(false, atomic::Ordering::AcqRel) {
            core.sync()?;
        }

        unsafe {
            let mmap = &mut *core.mmap.get();
            mem::ManuallyDrop::drop(mmap);
        }

        core.ffile.grow(len_to_add)?;

        let new_len = core.ffile.length()?;
        core.curr_length.store(new_len, atomic::Ordering::Release);

        unsafe {
            let new_map = TMap::new(core.ffile.fd(), new_len)?;
            *core.mmap.get() = mem::ManuallyDrop::new(new_map);
        };

        // resume all ops
        core.growing.store(false, atomic::Ordering::Release);

        core.shutdown_cv.notify_all();
        drop(guard);

        Ok(())
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        let length = self.length();
        unsafe { self.get_mmap().unmap(length) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.core.mmap.get() }
    }
}

impl<T> Drop for FrozenMMap<T>
where
    T: Clone + Sized + Send + Sync,
{
    fn drop(&mut self) {
        // close flusher thread
        self.core.cv.notify_one();

        // sync if dirty
        if self.core.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.core.sync();
        }

        let mut guard = match self.core.lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.core.active.load(atomic::Ordering::Acquire) != 0 {
            guard = match self.core.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(_) => return,
            }
        }

        // free up the boxed error (if any)
        let ptr = self.core.error.load(atomic::Ordering::Acquire);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }

        let _ = self.munmap();
    }
}

impl<T> fmt::Display for FrozenMMap<T>
where
    T: Clone + Sized + Send + Sync,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FrozenMMap{{fd: {}, len: {}}}", self.core.ffile.fd(), self.length())
    }
}

#[derive(Debug)]
struct Core {
    cv: sync::Condvar,
    ffile: FrozenFile,
    lock: sync::Mutex<()>,
    dirty: atomic::AtomicBool,
    active: atomic::AtomicU64,
    durable_cv: sync::Condvar,
    shutdown_cv: sync::Condvar,
    growing: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    write_epoch: atomic::AtomicU64,
    flush_duration: time::Duration,
    durable_epoch: atomic::AtomicU64,
    curr_length: atomic::AtomicUsize,
    error: atomic::AtomicPtr<FrozenErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, ffile: FrozenFile, flush_duration: time::Duration, curr_length: usize) -> Self {
        Self {
            ffile,
            flush_duration,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            durable_cv: sync::Condvar::new(),
            shutdown_cv: sync::Condvar::new(),
            active: atomic::AtomicU64::new(0),
            durable_lock: sync::Mutex::new(()),
            dirty: atomic::AtomicBool::new(false),
            write_epoch: atomic::AtomicU64::new(0),
            growing: atomic::AtomicBool::new(false),
            durable_epoch: atomic::AtomicU64::new(0),
            curr_length: atomic::AtomicUsize::new(curr_length),
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn curr_length(&self) -> usize {
        self.curr_length.load(atomic::Ordering::Acquire)
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        unsafe { (*self.mmap.get()).sync(self.curr_length()) }?;
        self.ffile.sync()
    }

    #[inline]
    fn set_sync_error(&self, err: FrozenErr) {
        let boxed = Box::into_raw(Box::new(err));
        let old = self.error.swap(boxed, atomic::Ordering::AcqRel);

        // NOTE: we must free the old error if any to avoid leaks
        if !old.is_null() {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
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
    fn clear_sync_error(&self) {
        let old = self.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old.is_null()) {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn acquire_guard(&self) -> FrozenRes<ActiveGuard<'_>> {
        // NOTE: this is fast path and will hold true in most of the calls, as `grow` is rare
        if hints::likely(!self.growing.load(atomic::Ordering::Acquire)) {
            self.active.fetch_add(1, atomic::Ordering::AcqRel);

            // NOTE: we recheck after increment to tackle close races
            if hints::likely(!self.growing.load(atomic::Ordering::Acquire)) {
                return Ok(ActiveGuard { core: self });
            }

            // must track back as grow started between check and increment
            self.active.fetch_sub(1, atomic::Ordering::Release);
        }

        // INFO: this is the slow path, and here we wait on `shutdown_cv` till grow is completed

        let mut guard = match self.lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
        };

        while self.growing.load(atomic::Ordering::Acquire) {
            guard = match self.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
            };
        }

        self.active.fetch_add(1, atomic::Ordering::AcqRel);
        drop(guard);

        Ok(ActiveGuard { core: self })
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<()> {
        let (tx, rx) = sync::mpsc::sync_channel::<FrozenRes<()>>(1);

        if let Err(error) = thread::Builder::new()
            .name("fm-flush-tx".into())
            .spawn(move || Self::tx_thread(core, tx))
        {
            let mut error = error.to_string().as_bytes().to_vec();
            error.extend_from_slice(b"Failed to spawn flush thread for FrozenMMap");
            return new_err(FMMapErrRes::Hcf, error);
        }

        if let Err(error) = rx.recv() {
            let mut error = error.to_string().as_bytes().to_vec();
            error.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");
            return new_err(FMMapErrRes::Hcf, error);
        }

        Ok(())
    }

    fn tx_thread(core: sync::Arc<Self>, init: sync::mpsc::SyncSender<FrozenRes<()>>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => {
                // NOTE: We can supress the error here, as this may never panic, unless the receiver
                // is shut, which is preveneted by design
                let _ = init.send(Ok(()));
                g
            }
            Err(error) => {
                if let Err(err) = init.send(new_err(FMMapErrRes::Unk, error.to_string().as_bytes().to_vec())) {
                    let mut message = err.to_string().as_bytes().to_vec();
                    message.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");
                    let error = FrozenErr::new(
                        unsafe { MODULE_ID },
                        ERRDOMAIN,
                        FMMapErrRes::Lpn as u16,
                        FMMapErrRes::Lpn.default_message(),
                        message,
                    );
                    core.set_sync_error(error);
                }
                return;
            }
        };

        // init done, now is detached from thread
        drop(init);

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FMMapErrRes::Txe, e));
                    return;
                }
            };

            // INFO: we must pause bg sync till grow is completed
            while core.growing.load(atomic::Ordering::Acquire) {
                guard = match core.shutdown_cv.wait(guard) {
                    Ok(g) => g,
                    Err(e) => {
                        core.set_sync_error(new_err_raw(FMMapErrRes::Txe, e));
                        return;
                    }
                };
            }

            if core.dirty.swap(false, atomic::Ordering::AcqRel) {
                drop(guard);

                // NOTE: if sync fails, we update the Core::error w/ the gathered error object,
                // and we clear it up when another sync call succeeds
                //
                // This is valid cause, the underlying sync, flushes entire mmaped region, so
                // even if the last call failed, and the new one succeeds, we do get the durability
                // guarenty for the old data as well

                match core.sync() {
                    Ok(_) => {
                        let current = core.write_epoch.load(atomic::Ordering::Acquire);
                        core.durable_epoch.store(current, atomic::Ordering::Release);

                        let _g = match core.durable_lock.lock() {
                            Ok(g) => g,
                            Err(e) => {
                                core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                                return;
                            }
                        };

                        core.durable_cv.notify_all();
                        core.clear_sync_error();
                    }
                    Err(err) => core.set_sync_error(err),
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                        return;
                    }
                };
            }
        }
    }
}

#[derive(Debug)]
struct ActiveGuard<'a> {
    core: &'a Core,
}

impl Drop for ActiveGuard<'_> {
    fn drop(&mut self) {
        if self.core.active.fetch_sub(1, atomic::Ordering::Release) == 1 {
            // last user
            if let Ok(_g) = self.core.lock.lock() {
                self.core.shutdown_cv.notify_one();
            }
        }
    }
}
