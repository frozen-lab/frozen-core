//! Custom implementation of `memmap`

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

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

/// default auto flush state for [`FMCfg`]
const AUTO_FLUSH: bool = false;

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
#[derive(Clone)]
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

    /// when true, all dirty pages would be synced by background thread
    pub auto_flush: bool,

    /// time interval for sync to flush dirty pages
    pub flush_duration: time::Duration,
}

impl FMCfg {
    /// Create a new instance of [`FMCfg`] w/ specified `module_id`
    pub const fn new(module_id: u8) -> Self {
        Self {
            module_id,
            auto_flush: AUTO_FLUSH,
            flush_duration: FLUSH_DURATION,
        }
    }

    /// Enable `auto_flush` for intervaled background sync for [`FrozenMMap`]
    pub const fn enable_auto_flush(mut self) -> Self {
        self.auto_flush = true;
        self
    }

    /// Set the interval for sync in [`FrozenMMap`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of MemMap
pub struct FrozenMMap(sync::Arc<Core>);

unsafe impl Send for FrozenMMap {}
unsafe impl Sync for FrozenMMap {}

impl FrozenMMap {
    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.0.length
    }

    /// Create a new [`FrozenMMap`] for given `fd` w/ read & write permissions
    pub fn new(file: FrozenFile, length: usize, cfg: FMCfg) -> FrozenRes<Self> {
        MID.store(cfg.module_id, atomic::Ordering::Relaxed);

        let mmap = unsafe { posix::POSIXMMap::new(file.fd(), length) }?;
        let core = sync::Arc::new(Core::new(mmap, cfg.clone(), length, file));

        if cfg.auto_flush {
            Core::spawn_tx(core.clone())?;
        }

        Ok(Self(core))
    }

    /// Syncs in-mem data on the storage device
    ///
    /// ## `F_FULLFSYNC` vs `msync`
    ///
    /// On mac (the supposed best os),`msync()` does not guarantee that the dirty pages are flushed
    /// by the storage device, and it may not physically write the data to the platters for
    /// quite some time
    ///
    /// More info [here](https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/msync.2.html)
    ///
    /// To achieve true crash durability (including protection against power loss),
    /// we must use `fcntl(fd, F_FULLFSYNC)` which provides strict durability guarantees
    ///
    /// If `F_FULLFSYNC` is not supported by the underlying filesystem or device
    /// (e.g., returns `EINVAL`, `ENOTSUP`, or `EOPNOTSUPP`), we fall back to
    /// `fsync()` as a best-effort persistence mechanism
    #[inline]
    pub fn sync(&self) -> FrozenRes<()> {
        let closed = self.0.dropped.load(atomic::Ordering::Acquire);
        if hints::unlikely(closed) {
            return new_err(FMMapErrRes::Hcf, b"Trying to access closed FrozenMMap".to_vec());
        }

        self.0.sync()
    }

    /// Get a [`FMReader`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn reader<'a, T>(&'a self, offset: usize) -> FrozenRes<FMReader<'a, T>> {
        self.0.acquire_instance()?;
        let reader = FMReader {
            ptr: unsafe { self.get_mmap().get(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(reader)
    }

    /// Get a [`FMWriter`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn writer<'a, T>(&'a self, offset: usize) -> FrozenRes<FMWriter<'a, T>> {
        self.0.acquire_instance()?;
        let writer = FMWriter {
            map: self,
            ptr: unsafe { self.get_mmap().get_mut(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(writer)
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        unsafe { self.get_mmap().unmap(self.length()) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.0.mmap.get() }
    }
}

impl Drop for FrozenMMap {
    fn drop(&mut self) {
        if self.0.dropped.swap(true, atomic::Ordering::AcqRel) {
            return;
        }

        // sync if dirty
        if self.0.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.sync();
        }

        let _ = self.munmap();
    }
}

impl fmt::Display for FrozenMMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{len: {}, id: {}, mode: {}}}",
            self.length(),
            self.0.cfg.module_id,
            self.0.cfg.auto_flush,
        )
    }
}

struct Core {
    cfg: FMCfg,
    length: usize,
    cv: sync::Condvar,
    _ffile: FrozenFile,
    lock: sync::Mutex<()>,
    dirty: atomic::AtomicBool,
    shutdown_cv: sync::Condvar,
    dropped: atomic::AtomicBool,
    active: atomic::AtomicUsize,
    error: sync::OnceLock<FrozenErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, cfg: FMCfg, length: usize, ffile: FrozenFile) -> Self {
        Self {
            cfg,
            length,
            _ffile: ffile,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            error: sync::OnceLock::new(),
            shutdown_cv: sync::Condvar::new(),
            active: atomic::AtomicUsize::new(0),
            dirty: atomic::AtomicBool::new(false),
            dropped: atomic::AtomicBool::new(false),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        unsafe {
            let mmap = &*self.mmap.get();

            #[cfg(target_os = "linux")]
            return mmap.sync(self.length);

            #[cfg(target_os = "macos")]
            return self._ffile.sync();
        }
    }

    #[inline]
    fn acquire_instance(&self) -> FrozenRes<()> {
        let mut cur = self.active.load(atomic::Ordering::Acquire);
        loop {
            if self.dropped.load(atomic::Ordering::Acquire) {
                return new_err(FMMapErrRes::Hcf, b"Trying to access unmapped FM".to_vec());
            }

            if let Err(v) =
                self.active
                    .compare_exchange_weak(cur, cur + 1, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                cur = v;
                continue;
            }

            return Ok(());
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
                    let _ = core.error.set(err);
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
                    let _ = core.error.set(err);
                    return;
                }
            };

            if core.dropped.load(atomic::Ordering::Acquire) {
                return;
            }

            if core.dirty.swap(false, atomic::Ordering::AcqRel) {
                drop(guard);

                if let Err(error) = core.sync() {
                    let _ = core.error.set(error);
                    return;
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        let res = FMMapErrRes::Lpn;
                        let detail = res.default_message();

                        let err =
                            FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                        let _ = core.error.set(err);
                        return;
                    }
                };
            }
        }
    }
}

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
pub struct FMWriter<'a, T> {
    ptr: *mut T,
    map: &'a FrozenMMap,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMWriter<'a, T> {
    /// Get's a mutable (read & write) typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, f: impl FnOnce(&mut T) -> R) -> FrozenRes<R> {
        let res = unsafe { f(&mut *self.ptr) };
        match self.map.0.cfg.auto_flush {
            false => self.map.sync()?,
            true => {
                self.map.0.dirty.store(true, atomic::Ordering::Release);
                self.map.0.cv.notify_one();
            }
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{error::TEST_MID, ffile::FrozenFile};
    use std::{sync::Arc, thread, time::Duration};

    const LEN: usize = 0x80;

    fn new_tmp(id: &'static [u8]) -> (Vec<u8>, FrozenFile, FrozenMMap) {
        let mut path = Vec::with_capacity(b"./target/".len() + id.len());
        path.extend_from_slice(b"./target/");
        path.extend_from_slice(id);

        let file = FrozenFile::new(path.clone(), LEN as u64, TEST_MID).expect("new FrozenFile");
        let cfg = FMCfg::new(TEST_MID);
        let mmap = FrozenMMap::new(file.clone(), LEN, cfg).expect("new FrozenMMap");

        (path, file, mmap)
    }

    mod fm_lifecycle {
        use super::*;

        #[test]
        fn map_drop_works() {
            let (_, file, mmap) = new_tmp(b"map_drop_works");
            drop(mmap);
            file.delete().expect("delete file");
        }
    }

    mod fm_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_, file, mmap) = new_tmp(b"sync_works");
            mmap.sync().expect("sync");
            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (path, file, mmap) = new_tmp(b"sync_persists");

            mmap.writer::<u64>(0x10)
                .expect("writer")
                .write(|v| *v = 0xABCD)
                .expect("write");

            mmap.sync().expect("sync");
            drop(mmap);

            let file2 = FrozenFile::new(path, LEN as u64, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file2.clone(), LEN, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0x10).expect("reader").read(|v| *v);
            assert_eq!(v, 0xABCD);

            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_, file, mmap) = new_tmp(b"repeated_sync");

            mmap.writer::<u64>(0).expect("writer").write(|v| *v = 7).expect("write");

            for _ in 0..0x20 {
                mmap.sync().expect("sync");
            }

            drop(mmap);
            file.delete().expect("delete file");
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_, file, mmap) = new_tmp(b"write_read_cycle");

            mmap.writer::<u64>(0)
                .expect("writer")
                .write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE)
                .expect("write");

            let v = mmap.reader::<u64>(0).expect("reader").read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);

            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn write_read_across_sessions() {
            let (path, file, mmap) = new_tmp(b"write_read_across_sessions");

            mmap.writer::<u64>(0)
                .expect("writer")
                .write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE)
                .expect("write");

            drop(mmap);
            drop(file);

            let file = FrozenFile::new(path, LEN as u64, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file.clone(), LEN, FMCfg::new(TEST_MID)).expect("new frozeMMap");

            let v = mmap.reader::<u64>(0).expect("reader").read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);

            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_, file, mmap) = new_tmp(b"multiple_writes");

            for i in 0..16u64 {
                mmap.writer::<u64>((i as usize) * 8)
                    .expect("writer")
                    .write(|v| *v = i)
                    .expect("write");
            }

            for i in 0..16u64 {
                let v = mmap.reader::<u64>((i as usize) * 8).expect("reader").read(|v| *v);
                assert_eq!(v, i);
            }

            drop(mmap);
            file.delete().expect("delete file");
        }
    }

    mod fm_concurrency {
        use super::*;

        #[test]
        fn concurrent_sync_is_safe() {
            let (_, file, mmap) = new_tmp(b"concurrent_sync");
            let mmap = Arc::new(mmap);

            mmap.writer::<u64>(0)
                .expect("writer")
                .write(|v| *v = 42)
                .expect("write");

            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.sync().expect("sync");
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            let v = mmap.reader::<u64>(0).expect("reader").read(|v| *v);
            assert_eq!(v, 42);

            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_, file, mmap) = new_tmp(b"concurrent_writes_offsets");
            let mmap = Arc::new(mmap);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.writer::<u64>((i as usize) * 8).unwrap().write(|v| *v = i).unwrap();
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

            drop(mmap);
            file.delete().expect("delete file");
        }

        #[test]
        fn auto_flush_background_thread() {
            let (_, file, mmap) = {
                let path = Vec::from(b"./target/auto_flush".as_slice());
                let file = FrozenFile::new(path.clone(), LEN as u64, TEST_MID).unwrap();
                let cfg = FMCfg::new(TEST_MID)
                    .enable_auto_flush()
                    .flush_duration(Duration::from_millis(10));
                let mmap = FrozenMMap::new(file.clone(), LEN, cfg).unwrap();
                (path, file, mmap)
            };

            mmap.writer::<u64>(0).unwrap().write(|v| *v = 99).unwrap();
            thread::sleep(Duration::from_millis(50));

            let v = mmap.reader::<u64>(0).unwrap().read(|v| *v);
            assert_eq!(v, 99);

            drop(mmap);
            file.delete().expect("delete file");
        }
    }
}
