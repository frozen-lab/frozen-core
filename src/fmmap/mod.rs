//! Custom implementation of `memmap`
//!
//! # Example Usage
//!
//! ```
//! use frozen_core::{ffile::FrozenFile, fmmap::{FrozenMMap, FMCfg}};
//! use tempfile::tempdir;
//!
//! let dir = tempdir().expect("tmp dir");
//! let path = dir.path().join("example.bin");
//!
//! let file = FrozenFile::new(path, 0x10, 1).expect("file");
//! let mmap = FrozenMMap::new(file, FMCfg::new(1)).expect("mmap");
//! let (_, epoch) = mmap.with_write::<u64, _>(0, |v| *v = 0xDEADC0DE).expect("write");
//!
//! match mmap.wait_for_durability(epoch) {
//!     Ok(_) => {
//!         let value = mmap.with_read::<u64, u64>(0, |v| *v).unwrap();
//!         assert_eq!(value, 0xDEADC0DE);
//!     }
//!     Err(e) => panic!("{e}"),
//! }
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{FrozenErr, FrozenRes},
    ffile::FrozenFile,
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

/// default flush duration for [`FMCfg`]
const FLUSH_DURATION: time::Duration = time::Duration::from_millis(250);

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenErr`]
static MID: atomic::AtomicU8 = atomic::AtomicU8::new(0);

#[inline]
pub(in crate::fmmap) fn mid() -> u8 {
    MID.load(atomic::Ordering::Relaxed)
}

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
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

/// Config for [`FrozenMMap`]
#[derive(Debug, Clone)]
pub struct FMCfg {
    /// module id for [`FrozenMMap`]
    ///
    /// This id is used for error codes
    ///
    /// ## Why
    ///
    /// It enables for easier identification of error boundries when multiple [`FrozenMMap`]
    /// modules are present in the codebase
    pub module_id: u8,

    /// time interval for sync to flush dirty pages
    pub flush_duration: time::Duration,
}

impl FMCfg {
    /// Create a new instance of [`FMCfg`] w/ specified `module_id`
    pub const fn new(module_id: u8) -> Self {
        Self {
            module_id,
            flush_duration: FLUSH_DURATION,
        }
    }

    /// Set the interval for sync in [`FrozenMMap`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of MemMap
///
/// # Example
///
/// ```
/// use frozen_core::{ffile::FrozenFile, fmmap::{FrozenMMap, FMCfg}};
/// use tempfile::tempdir;
///
/// let dir = tempdir().expect("tmp dir");
/// let path = dir.path().join("example.bin");
///
/// let file = FrozenFile::new(path, 0x10, 1).expect("file");
/// let mmap = FrozenMMap::new(file, FMCfg::new(1)).expect("mmap");
/// let (_, epoch) = mmap.with_write::<u64, _>(0, |v| *v = 0xDEADC0DE).expect("write");
///
/// match mmap.wait_for_durability(epoch) {
///     Ok(_) => {
///         let value = mmap.with_read::<u64, u64>(0, |v| *v).unwrap();
///         assert_eq!(value, 0xDEADC0DE);
///     }
///     Err(e) => panic!("{e}"),
/// }
/// ```
#[derive(Debug)]
pub struct FrozenMMap(sync::Arc<Core>);

unsafe impl Send for FrozenMMap {}
unsafe impl Sync for FrozenMMap {}

impl FrozenMMap {
    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.0.ffile.length()
    }

    /// Create a new [`FrozenMMap`] for given `fd` w/ read & write permissions
    pub fn new(file: FrozenFile, cfg: FMCfg) -> FrozenRes<Self> {
        MID.store(cfg.module_id, atomic::Ordering::Relaxed);

        let mmap = unsafe { posix::POSIXMMap::new(file.fd(), file.length()) }?;
        let core = sync::Arc::new(Core::new(mmap, cfg.clone(), file));

        // INFO: we spawn the thread for background sync
        Core::spawn_tx(core.clone())?;

        Ok(Self(core))
    }

    /// Returns the [`FrozenErr`] representing the last error occurred in [`FrozenMMap`]
    #[inline]
    pub fn last_error(&self) -> Option<&FrozenErr> {
        self.0.get_sync_error()
    }

    /// Wait for durability for the given write `epoch`
    ///
    /// This functions blocks until epoch becomes durable
    ///
    /// # Example
    ///
    /// ```
    /// use frozen_core::{ffile::FrozenFile, fmmap::{FrozenMMap, FMCfg}};
    /// use tempfile::tempdir;
    ///
    /// let dir = tempdir().expect("tmp");
    /// let path = dir.path().join("durable.bin");
    ///
    /// let file = FrozenFile::new(path, 0x10, 1).expect("file");
    /// let mmap = FrozenMMap::new(file, FMCfg::new(1)).expect("mmap");
    /// let (_, epoch) = mmap.with_write::<u64, _>(0, |v| *v = 1).expect("write");
    ///
    /// match mmap.wait_for_durability(epoch) {
    ///     Ok(_) => {
    ///         let value = mmap.with_read::<u64, u64>(0, |v| *v).unwrap();
    ///         assert_eq!(value, 1);
    ///     }
    ///     Err(e) => panic!("{e}"),
    /// }
    /// ```
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        if self.0.durable_epoch.load(atomic::Ordering::Acquire) >= epoch {
            return Ok(());
        }

        let mut guard = match self.0.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
        };

        while self.0.durable_epoch.load(atomic::Ordering::Acquire) < epoch {
            guard = match self.0.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
            }
        }

        Ok(())
    }

    /// Get's a read only typed pointer for `T`
    #[inline]
    pub fn with_read<T, R>(&self, offset: usize, f: impl FnOnce(&T) -> R) -> FrozenRes<R> {
        let guard = self.acquire_guard()?;

        let ptr = unsafe { self.get_mmap().get(offset) };
        let res = unsafe { f(&*ptr) };

        drop(guard);
        Ok(res)
    }

    /// Get's a mutable typed pointer for `T`
    #[inline]
    pub fn with_write<T, R>(&self, offset: usize, f: impl FnOnce(&mut T) -> R) -> FrozenRes<(R, TEpoch)> {
        let guard = self.acquire_guard()?;

        let ptr = unsafe { self.get_mmap().get_mut(offset) };
        let res = unsafe { f(&mut *ptr) };
        let epoch = self.0.write_epoch.fetch_add(1, atomic::Ordering::AcqRel) + 1;

        self.0.dirty.store(true, atomic::Ordering::Release);

        drop(guard);
        Ok((res, epoch))
    }

    /// Get a [`FMReader`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn reader<T>(&self, offset: usize) -> FrozenRes<FMReader<'_, T>> {
        let guard = self.acquire_guard()?;
        let reader = FMReader {
            ptr: unsafe { self.get_mmap().get(offset) },
            _guard: guard,
        };

        Ok(reader)
    }

    /// Get a [`FMWriter`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn writer<'a, T>(&'a self, offset: usize) -> FrozenRes<FMWriter<'a, T>> {
        let guard = self.acquire_guard()?;
        let writer = FMWriter {
            map: self,
            ptr: unsafe { self.get_mmap().get_mut(offset) },
            _guard: guard,
        };

        Ok(writer)
    }

    /// grow [`FrozenMMap`] by given `len_to_add`, by growing underlying [`FrozenFile`]
    /// and re-mapping on the grown region
    pub fn grow(&self, len_to_add: usize) -> FrozenRes<()> {
        let core = &self.0;

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
        unsafe {
            let new_map = posix::POSIXMMap::new(core.ffile.fd(), core.ffile.length())?;
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
        unsafe { self.get_mmap().unmap(self.length()) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.0.mmap.get() }
    }

    #[inline]
    fn acquire_guard(&self) -> FrozenRes<ActiveGuard<'_>> {
        let core = &self.0;

        // NOTE: this is fast path and will hold true in most of the calls, as `grow` is rare
        if hints::likely(!core.growing.load(atomic::Ordering::Acquire)) {
            core.active.fetch_add(1, atomic::Ordering::AcqRel);

            // NOTE: we recheck after increment to tackle close races
            if hints::likely(!core.growing.load(atomic::Ordering::Acquire)) {
                return Ok(ActiveGuard { core });
            }

            // must track back as grow started between check and increment
            core.active.fetch_sub(1, atomic::Ordering::Release);
        }

        // INFO: this is the slow path, and here we wait on `shutdown_cv` till grow is completed

        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
        };

        while core.growing.load(atomic::Ordering::Acquire) {
            guard = match core.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(FMMapErrRes::Lpn, e.to_string().as_bytes().to_vec()),
            };
        }

        core.active.fetch_add(1, atomic::Ordering::AcqRel);
        drop(guard);

        Ok(ActiveGuard { core })
    }
}

impl Drop for FrozenMMap {
    fn drop(&mut self) {
        // close flusher thread
        self.0.cv.notify_one();

        // sync if dirty
        if self.0.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.0.sync();
        }

        let mut guard = match self.0.lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.0.active.load(atomic::Ordering::Acquire) != 0 {
            guard = match self.0.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(_) => return,
            }
        }

        // free up the boxed error (if any)
        let ptr = self.0.error.load(atomic::Ordering::Acquire);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }

        let _ = self.munmap();
    }
}

impl fmt::Display for FrozenMMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{len: {}, mod_id: {}, fd: {}}}",
            self.length(),
            self.0.cfg.module_id,
            self.0.ffile.fd(),
        )
    }
}

#[derive(Debug)]
struct Core {
    cfg: FMCfg,
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
    durable_epoch: atomic::AtomicU64,
    error: atomic::AtomicPtr<FrozenErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, cfg: FMCfg, ffile: FrozenFile) -> Self {
        Self {
            cfg,
            ffile,
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
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        #[cfg(target_os = "linux")]
        unsafe {
            let mmap = &*self.mmap.get();
            return mmap.sync(self.ffile.length());
        }

        #[cfg(target_os = "macos")]
        return self.ffile.sync();
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
    fn get_sync_error(&self) -> Option<&FrozenErr> {
        let ptr = self.error.load(atomic::Ordering::Acquire);

        if hints::likely(ptr.is_null()) {
            return None;
        }

        Some(unsafe { &*ptr })
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
                    let res = FMMapErrRes::Lpn;
                    let detail = res.default_message();

                    let mut err_msg = err.to_string().as_bytes().to_vec();
                    err_msg.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");

                    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, err_msg);
                    core.set_sync_error(err);
                }
                return;
            }
        };

        // init done, now is detached from thread
        drop(init);

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.cfg.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    let res = FMMapErrRes::Txe;
                    let detail = res.default_message();

                    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                    core.set_sync_error(err);
                    return;
                }
            };

            // INFO: we must pause bg sync till grow is completed
            while core.growing.load(atomic::Ordering::Acquire) {
                guard = match core.shutdown_cv.wait(guard) {
                    Ok(g) => g,
                    Err(e) => {
                        let res = FMMapErrRes::Txe;
                        let detail = res.default_message();

                        let err =
                            FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                        core.set_sync_error(err);
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
                                let res = FMMapErrRes::Lpn;
                                let detail = res.default_message();

                                let err = FrozenErr::new(
                                    mid(),
                                    ERRDOMAIN,
                                    res as u16,
                                    detail,
                                    e.to_string().as_bytes().to_vec(),
                                );
                                core.set_sync_error(err);
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
                        let res = FMMapErrRes::Lpn;
                        let detail = res.default_message();

                        let err =
                            FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                        core.set_sync_error(err);
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

/// Reader object for [`FrozenMMap`]
#[derive(Debug)]
pub struct FMReader<'a, T> {
    ptr: *const T,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMReader<'a, T> {
    /// Get's an immutable (read only) typed pointer for `T`
    #[inline]
    pub fn read<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        unsafe { f(&*self.ptr) }
    }
}

/// Writer object for [`FrozenMMap`]
#[derive(Debug)]
pub struct FMWriter<'a, T> {
    ptr: *mut T,
    map: &'a FrozenMMap,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMWriter<'a, T> {
    /// Get's a mutable (read & write) typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, f: impl FnOnce(&mut T) -> R) -> (R, TEpoch) {
        let res = unsafe { f(&mut *self.ptr) };
        let epoch = self.map.0.write_epoch.fetch_add(1, atomic::Ordering::AcqRel) + 1;

        self.map.0.dirty.store(true, atomic::Ordering::Release);

        (res, epoch)
    }

    /// Get's a mutable (read & write) typed pointer for `T`
    ///
    /// ## NOTE
    ///
    /// This function notifies sync thread for sync operation right after `f()` is computed,
    /// skipping the `[FMCfg::flush_duration]`
    ///
    /// Only use this for instant flush, overuse may strain the available resources
    #[inline]
    pub fn write_instant<R>(&self, f: impl FnOnce(&mut T) -> R) -> (R, TEpoch) {
        let res = unsafe { f(&mut *self.ptr) };
        let epoch = self.map.0.write_epoch.fetch_add(1, atomic::Ordering::AcqRel) + 1;

        self.map.0.dirty.store(true, atomic::Ordering::Release);
        self.map.0.cv.notify_one();

        (res, epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{error::TEST_MID, ffile::FrozenFile};
    use std::{path::PathBuf, sync::Arc, thread};
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x80;

    fn new_tmp() -> (TempDir, PathBuf, FrozenMMap) {
        let dir = tempdir().expect("tmp dir");
        let path = dir.path().join("ids");

        let file = FrozenFile::new(path.clone(), LEN, TEST_MID).expect("new FrozenFile");
        let cfg = FMCfg::new(TEST_MID);
        let mmap = FrozenMMap::new(file, cfg).expect("new FrozenMMap");

        (dir, path, mmap)
    }

    mod fm_new {
        use super::*;

        #[test]
        fn new_works() {
            let (_dir, _path, mmap) = new_tmp();

            assert!(mmap.0.ffile.fd() >= 0);
            assert_eq!(mmap.0.ffile.length(), LEN);
            assert!(!mmap.0.dirty.load(atomic::Ordering::Relaxed));
            assert_eq!(mmap.0.active.load(atomic::Ordering::Relaxed), 0);
            assert!(mmap.last_error().is_none());
        }
    }

    mod fm_lifetime {
        use super::*;

        #[test]
        fn drop_without_dirty_is_safe() {
            let (_dir, _path, mmap) = new_tmp();
            drop(mmap);
        }

        #[test]
        fn last_error_initially_none() {
            let (_dir, _path, mmap) = new_tmp();
            assert!(mmap.last_error().is_none());
        }
    }

    mod fm_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _path, mmap) = new_tmp();
            mmap.0.sync().expect("sync");
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (_dir, path, mmap) = new_tmp();

            let _ = mmap.writer::<u64>(0x10).unwrap().write(|v| *v = 0xABCD);

            mmap.0.sync().expect("sync");
            drop(mmap);

            let file2 = FrozenFile::new(path, LEN, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file2, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0x10).unwrap().read(|v| *v);
            assert_eq!(v, 0xABCD);
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 7);

            for _ in 0..0x20 {
                mmap.0.sync().expect("sync");
            }
        }
    }

    mod fm_auto_flush {
        use super::*;

        #[test]
        fn auto_flush_persists() {
            let dir = tempdir().expect("tmp dir");
            let path = dir.path().join("ids");

            let file = FrozenFile::new(path.clone(), LEN, TEST_MID).unwrap();

            let cfg = FMCfg::new(TEST_MID).flush_duration(std::time::Duration::from_millis(50));

            let mmap = FrozenMMap::new(file, cfg).unwrap();

            let _ = mmap.writer::<u64>(0).unwrap().write(|v| *v = 123);

            thread::sleep(std::time::Duration::from_millis(150));

            drop(mmap);

            let file = FrozenFile::new(path, LEN, TEST_MID).unwrap();
            let mmap = FrozenMMap::new(file, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            assert_eq!(v, 123);
        }
    }

    mod fm_with_api {
        use super::*;

        #[test]
        fn with_write_then_read() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.with_write::<u64, _>(0, |v| *v = 99).unwrap();

            let v = mmap.with_read::<u64, _>(0, |v| *v).unwrap();
            assert_eq!(v, 99);
        }

        #[test]
        fn with_write_multiple_offsets() {
            let (_dir, _path, mmap) = new_tmp();

            for i in 0..8u64 {
                mmap.with_write::<u64, _>((i as usize) * 8, |v| *v = i).unwrap();
            }

            for i in 0..8u64 {
                let v = mmap.with_read::<u64, _>((i as usize) * 8, |v| *v).unwrap();
                assert_eq!(v, i);
            }
        }
    }

    mod fm_active_drain {
        use super::*;

        #[test]
        fn drop_waits_for_reader() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let m = mmap.clone();
            let handle = thread::spawn(move || {
                let r = m.reader::<u64>(0);
                thread::sleep(std::time::Duration::from_millis(50));
                drop(r);
            });

            thread::sleep(std::time::Duration::from_millis(10));
            drop(mmap); // must wait for reader

            handle.join().expect("join");
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn active_counter_tracks_readers() {
            let (_dir, _path, mmap) = new_tmp();

            let r1 = mmap.reader::<u64>(0);
            let r2 = mmap.reader::<u64>(0);

            assert!(mmap.0.active.load(std::sync::atomic::Ordering::Acquire) >= 2);

            drop(r1);
            drop(r2);
        }

        #[test]
        fn write_read_cycle() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE);

            let v = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, path, mmap) = new_tmp();

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE);

            drop(mmap);

            let file = FrozenFile::new(path, LEN, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file, FMCfg::new(TEST_MID)).expect("new frozeMMap");

            let v = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_dir, _path, mmap) = new_tmp();

            for i in 0..16u64 {
                mmap.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i);
            }

            for i in 0..16u64 {
                let v = mmap.reader::<u64>((i as usize) * 8).unwrap().read(|v| *v);
                assert_eq!(v, i);
            }
        }
    }

    mod fm_grow {
        use super::*;

        #[test]
        fn grow_extends_and_preserves_data() {
            let (_dir, _path, mmap) = new_tmp();

            // NOTE: this assumes that the file is already init'd w/ `LEN` as `init_len`

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 111);
            mmap.grow(LEN).expect("grow");
            mmap.writer::<u64>(LEN).unwrap().write(|v| *v = 222);

            let a = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            let b = mmap.reader::<u64>(0x80).unwrap().read(|v| *v);

            assert_eq!(a, 111);
            assert_eq!(b, 222);
        }

        #[test]
        fn grow_persists_across_reopen() {
            let (_dir, path, mmap) = new_tmp();

            mmap.grow(0x100).expect("grow");
            mmap.writer::<u64>(0x80).unwrap().write(|v| *v = 999);

            drop(mmap);

            let file = FrozenFile::new(path, LEN + 0x100, TEST_MID).unwrap();
            let mmap = FrozenMMap::new(file, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0x80).unwrap().read(|v| *v);
            assert_eq!(v, 999);
        }

        #[test]
        fn grow_blocks_readers() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let m = mmap.clone();
            let handle = thread::spawn(move || {
                m.grow(0x200).expect("grow");
            });

            // attempt concurrent read during grow
            let m2 = mmap.clone();
            let r = thread::spawn(move || {
                let _ = m2.reader::<u64>(0).unwrap();
            });

            handle.join().unwrap();
            r.join().unwrap();
        }

        #[test]
        fn grow_under_concurrent_writes() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let m1 = mmap.clone();
            let writer = thread::spawn(move || {
                for i in 0..0x20u64 {
                    m1.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i);
                }
            });

            let m2 = mmap.clone();
            let grower = thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(10));
                m2.grow(0x200).expect("grow");
            });

            writer.join().unwrap();
            grower.join().unwrap();
        }
    }

    mod fm_concurrency {
        use super::*;

        #[test]
        fn concurrent_sync_is_safe() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 42);

            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.0.sync().expect("sync");
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            let v = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            assert_eq!(v, 42);
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i);
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            for i in 0..8u64 {
                let v = mmap.reader::<u64>((i as usize) * 8).unwrap().read(|v| *v);
                assert_eq!(v, i);
            }
        }

        #[test]
        fn concurrent_with_write() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.with_write::<u64, _>((i as usize) * 8, |v| *v = i).unwrap();
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("join");
            }

            for i in 0..8u64 {
                let v = mmap.with_read::<u64, _>((i as usize) * 8, |v| *v).unwrap();
                assert_eq!(v, i);
            }
        }
    }

    mod fm_epoch {
        use super::*;

        #[test]
        fn epoch_monotonicity() {
            let (_dir, _path, mmap) = new_tmp();

            let (_, e1) = mmap.writer::<u64>(0).unwrap().write(|v| *v = 1);
            let (_, e2) = mmap.writer::<u64>(8).unwrap().write(|v| *v = 2);
            let (_, e3) = mmap.writer::<u64>(16).unwrap().write(|v| *v = 3);

            assert!(e1 < e2);
            assert!(e2 < e3);
        }

        #[test]
        fn wait_for_durability_blocks_until_flush() {
            let (_dir, _path, mmap) = new_tmp();

            let (_, epoch) = mmap.writer::<u64>(0).unwrap().write(|v| *v = 10);

            // Should block until background flush occurs
            mmap.wait_for_durability(epoch).expect("wait");

            assert!(mmap.0.durable_epoch.load(std::sync::atomic::Ordering::Acquire) >= epoch);
        }

        #[test]
        fn wait_returns_immediately_if_already_durable() {
            let (_dir, _path, mmap) = new_tmp();

            let (_, epoch) = mmap.writer::<u64>(0).unwrap().write(|v| *v = 11);

            mmap.wait_for_durability(epoch).expect("wait");

            // second call must return immediately
            mmap.wait_for_durability(epoch).expect("wait again");
        }

        #[test]
        fn multiple_waiters_are_notified() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let (_, epoch) = mmap.writer::<u64>(0).unwrap().write(|v| *v = 99);

            let mut handles = Vec::new();

            for _ in 0..4 {
                let m = mmap.clone();
                handles.push(thread::spawn(move || {
                    m.wait_for_durability(epoch).expect("wait");
                }));
            }

            for h in handles {
                h.join().expect("join");
            }

            assert!(mmap.0.durable_epoch.load(std::sync::atomic::Ordering::Acquire) >= epoch);
        }

        #[test]
        fn durable_epoch_tracks_latest_write() {
            let (_dir, _path, mmap) = new_tmp();

            let mut last = 0;

            for i in 0..8u64 {
                let (_, e) = mmap.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i);
                last = e;
            }

            mmap.wait_for_durability(last).expect("wait");

            let durable = mmap.0.durable_epoch.load(std::sync::atomic::Ordering::Acquire);

            assert!(durable >= last);
        }

        #[test]
        fn concurrent_wait_and_writes() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let m_writer = mmap.clone();
            let writer = thread::spawn(move || {
                let mut last = 0;
                for i in 0..16u64 {
                    let (_, e) = m_writer.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i);
                    last = e;
                }
                last
            });

            let m_waiter = mmap.clone();
            let waiter = thread::spawn(move || {
                let target = writer.join().expect("join writer");
                m_waiter.wait_for_durability(target).expect("wait");
            });

            waiter.join().expect("join waiter");

            let durable = mmap.0.durable_epoch.load(std::sync::atomic::Ordering::Acquire);

            assert!(durable >= mmap.0.write_epoch.load(std::sync::atomic::Ordering::Acquire));
        }
    }
}
