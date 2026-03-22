//! Custom implementation of `mmap(2)`
//!
//! ## Constraints
//!
//! [`FrozenMMap`] treats the mapped file as raw storage for values of `T`. Because of that, `T` must be a POD type
//! which is safe to persist and later reinterpret from bytes.
//!
//! Required properties for `T`,
//!
//! - Must use `#[repr(C)]`
//! - Should be 8-bytes aligned
//! - Must not implement [`Drop`]
//! - `size_of::<T>()` should be multiple of `8`
//!
//! *NOTE:* `T` must not contain heap owning or process-local pointers like [`Vec`], [`String`], [`Box`], references
//! and function pointers, or other fields whose bit-pattern is not stable across reopen.
//!
//! These constrains are enforced as [`FrozenMMap`] does not serialize or deserialize values. It directly reads and
//! writes `T` inside a memory mapped file. That means `T` must have a stable layout and must remain valid when the file
//! is reopened in a later process.
//!
//! ## Example
//!
//! ```
//! use frozen_core::fmmap::{FrozenMMap, FMCfg};
//!
//! const MODULE_ID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_mmap");
//!
//! let cfg = FMCfg {
//!     initial_count: 0x0A,
//!     flush_duration: std::time::Duration::from_micros(0x96),
//! };
//!
//! let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg.clone()).unwrap();
//! assert_eq!(mmap.total_slots(), 0x0A);
//!
//! let epoch = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
//! mmap.wait_for_durability(epoch).unwrap();
//!
//! let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//!
//! drop(mmap);
//!
//! let reopened = FrozenMMap::<u64, MODULE_ID>::new_grown(&path, cfg, 0x05).unwrap();
//! assert_eq!(reopened.total_slots(), 0x0A + 0x05);
//!
//! let val = unsafe { reopened.read(0, |v| *v) }.unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{ErrCode, FrozenErr, FrozenRes},
    ffile::{FFCfg, FrozenFile},
    hints,
};
use std::{
    fmt,
    sync::{self, atomic},
    thread, time,
};

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

/// type for `epoch` used by write ops
pub type TEpoch = u64;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenMMap`]
static MID: sync::OnceLock<u8> = sync::OnceLock::new();

#[cfg(not(test))]
#[inline(always)]
fn mid() -> &'static u8 {
    MID.get().unwrap()
}

#[cfg(test)]
#[inline(always)]
fn mid() -> &'static u8 {
    MID.get_or_init(|| 0)
}

/// Error codes for [`FrozenMMap`]
pub(in crate::fmmap) mod err {
    use super::ErrCode;

    /// (512) internal fuck up (hault and catch fire)
    pub const HCF: ErrCode = ErrCode::new(0x200, "hault and catch fire");

    /// (513) unknown error (fallback)
    pub const UNK: ErrCode = ErrCode::new(0x201, "unknown error");

    /// (514) no more memory available
    pub const NMM: ErrCode = ErrCode::new(0x202, "not enough memory available on the device");

    /// (515) syncing error
    pub const SYN: ErrCode = ErrCode::new(0x203, "failed to sync/flush data to storage device");

    /// (516) no write/read perm
    pub const PRM: ErrCode = ErrCode::new(0x204, "missing permissions for IO");

    /// (517) flush_tx error (panic inside)
    pub const TXE: ErrCode = ErrCode::new(0x205, "flush_tx paniced inside");

    /// (518) flush_tx error (unable to spawn)
    pub const FXE: ErrCode = ErrCode::new(0x206, "unable to spawn flush_tx");

    /// (519) lock poisoned
    pub const LPN: ErrCode = ErrCode::new(0x207, "lock poisoned internally");

    /// (520) type `T` implements drop
    pub const DRP: ErrCode = ErrCode::new(0x208, "type T must not implement `Drop`");

    /// (521) type `T` is not 8 bytes aligned
    pub const ALN: ErrCode = ErrCode::new(0x209, "type T must be 8-bytes aligned");

    /// (522) `size_of::<T>()` is not multiple of 8
    pub const SZE: ErrCode = ErrCode::new(0x20A, "`size_of::<T>()` must be multiple of 8 bytes");

    /// (523) type `T` must not be zero sized
    pub const ZRO: ErrCode = ErrCode::new(0x20B, "type T must not be zero sized");
}

#[inline]
pub(in crate::fmmap) fn new_err<R, E: std::fmt::Display>(code: ErrCode, error: E) -> FrozenRes<R> {
    let err = FrozenErr::new_raw(*mid(), ERRDOMAIN, code, error);
    Err(err)
}

#[inline]
pub(in crate::fmmap) fn new_err_default<R>(code: ErrCode) -> FrozenRes<R> {
    let err = FrozenErr::new_raw(*mid(), ERRDOMAIN, code, "");
    Err(err)
}

#[inline]
pub(in crate::fmmap) fn new_err_raw<E: std::fmt::Display>(code: ErrCode, error: E) -> FrozenErr {
    FrozenErr::new_raw(*mid(), ERRDOMAIN, code, error)
}

/// Config for [`FrozenMMap`]
#[derive(Debug, Clone)]
pub struct FMCfg {
    /// Number of slots to pre-allocate when [`FrozenMMap`] is initialized
    ///
    /// Each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`], where initial file length will
    /// be `chunk_size * initial_count` (bytes)
    pub initial_count: usize,

    /// Time interval used by flusher tx, to batch write ops into a durable window and sync them
    /// together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,
}

/// Custom implementation of `mmap(2)`
///
/// ## Constraints
///
/// [`FrozenMMap`] treats the mapped file as raw storage for values of `T`. Because of that, `T` must be a POD type
/// which is safe to persist and later reinterpret from bytes.
///
/// Required properties for `T`,
///
/// - Must use `#[repr(C)]`
/// - Should be 8-bytes aligned
/// - Must not implement [`Drop`]
/// - `size_of::<T>()` should be multiple of `8`
///
/// *NOTE:* `T` must not contain heap owning or process-local pointers like [`Vec`], [`String`], [`Box`], references
/// and function pointers, or other fields whose bit-pattern is not stable across reopen.
///
/// These constrains are enforced as [`FrozenMMap`] does not serialize or deserialize values. It directly reads and
/// writes `T` inside a memory mapped file. That means `T` must have a stable layout and must remain valid when the file
/// is reopened in a later process.
///
/// ## Example
///
/// ```
/// use frozen_core::fmmap::{FrozenMMap, FMCfg};
///
/// const MODULE_ID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_mmap");
///
/// let cfg = FMCfg {
///     initial_count: 0x0A,
///     flush_duration: std::time::Duration::from_micros(0x96),
/// };
///
/// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg.clone()).unwrap();
/// assert_eq!(mmap.total_slots(), 0x0A);
///
/// let epoch = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
/// mmap.wait_for_durability(epoch).unwrap();
///
/// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
/// assert_eq!(val, 0xDEADC0DE);
///
/// drop(mmap);
///
/// let reopened = FrozenMMap::<u64, MODULE_ID>::new_grown(&path, cfg, 0x05).unwrap();
/// assert_eq!(reopened.total_slots(), 0x0A + 0x05);
///
/// let val = unsafe { reopened.read(0, |v| *v) }.unwrap();
/// assert_eq!(val, 0xDEADC0DE);
/// ```
#[derive(Debug)]
pub struct FrozenMMap<T, const MODULE_ID: u8>
where
    T: Sized + Send + Sync,
{
    core: sync::Arc<Core>,
    tx: Option<thread::JoinHandle<()>>,
    _t: core::marker::PhantomData<T>,
}

unsafe impl<T, const MODULE_ID: u8> Send for FrozenMMap<T, MODULE_ID> where T: Sized + Send + Sync {}
unsafe impl<T, const MODULE_ID: u8> Sync for FrozenMMap<T, MODULE_ID> where T: Sized + Send + Sync {}

impl<T, const MODULE_ID: u8> FrozenMMap<T, MODULE_ID>
where
    T: Sized + Send + Sync,
{
    /// Memory space required for each slot of [`T`] in [`FrozenMMap`]
    pub const SLOT_SIZE: usize = std::mem::size_of::<T>();

    /// Create a new [`FrozenMMap`] instance w/ given [`FMCfg`]
    ///
    /// ## Multiple Instances
    ///
    /// For each [`FrozenMMap`] instance, we acquire an exclusive lock from the kernal for the underlying [`FrozenFile`],
    /// when trying to create multiple instances of [`FrozenMMap`], an error will be thrown    ///
    ///
    /// ## Capacity Growth
    ///
    /// [`FrozenMMap`] does not support in-place growth of a live mapping, to increase capacity, drop the current instance
    /// and reopen w/ [`FrozenMMap::open_grown`] which provides memory mapping over grown capacity
    ///
    /// ## [`FMCfg`]
    ///
    /// All configs for [`FrozenMMap`] are stored in [`FMCfg`]
    ///
    /// ## Working
    ///
    /// We first create a new [`FrozenFile`] if note already, then map the entire file using `mmap(2)`,
    /// the entire file must read/write `T`, which also should stay constant for the entire lifetime of file
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`], which is used under
    /// the hood, one must use config stores like [`Rta`](https://crates.io/crates/rta) to store config
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x0A,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg.clone()).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x0A);
    ///
    /// let epoch = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0xDEADC0DE);
    /// ```
    pub fn new<P: AsRef<std::path::Path>>(path: P, cfg: FMCfg) -> FrozenRes<Self> {
        Self::validate_t()?;
        let (file, curr_length) = Self::open_file(path.as_ref().to_path_buf(), &cfg)?;
        let total_slots = curr_length / Self::SLOT_SIZE;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock` guarantees that the
        // first caller sets the value and all subsequent calls reuse it
        let _ = MID.get_or_init(|| MODULE_ID);

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, cfg.flush_duration, curr_length, total_slots));

        // INFO: we spawn the thread for background sync
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self {
            core,
            tx: Some(tx),
            _t: core::marker::PhantomData,
        })
    }

    /// Create a new [`FrozenMMap`] instance w/ given [`FMCfg`], while growing the underlying [`FrozenFile`]
    /// by `additional_slots` before creating memory mapping
    ///
    /// ## Multiple Instances
    ///
    /// For each [`FrozenMMap`] instance, we acquire an exclusive lock from the kernal for the underlying [`FrozenFile`],
    /// when trying to create multiple instances of [`FrozenMMap`], an error will be thrown
    ///
    /// ## Why not create a [`FrozenMMap::grow`] call?
    ///
    /// Previously when [`FrozenMMap::grow`] was attempted, it was observed that, resizing an active memory mapping
    /// in place is tricky in concurrent code, as some threads would still hold stale/unmapped pointers to mmap
    /// due to preemption from the OS schedular
    ///
    /// So, instead of remmaping a live instance, the current API performs growth during open, making capacity expansion
    /// an explicit lifecycle operation, and not a side effect on a live instance
    ///
    /// ## [`FMCfg`]
    ///
    /// All configs for [`FrozenMMap`] are stored in [`FMCfg`]
    ///
    /// ## Working
    ///
    /// We first create a new [`FrozenFile`] if note already, then we grow the file using [`FrozenFile::grow`]
    /// then map the entire file using `mmap(2)`, the entire file must read/write `T`, which also should stay
    /// constant for the entire lifetime of file
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`], which is used under
    /// the hood, one must use config stores like [`Rta`](https://crates.io/crates/rta) to store config
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x0A,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new_grown(&path, cfg.clone(), 0x0A).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x0A * 2);
    ///
    /// let epoch = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0xDEADC0DE);
    /// ```
    pub fn new_grown<P: AsRef<std::path::Path>>(path: P, cfg: FMCfg, additional_slots: usize) -> FrozenRes<Self> {
        Self::validate_t()?;
        let (file, _) = Self::open_file(path.as_ref().to_path_buf(), &cfg)?;

        // we grow the underlying FrozenFile as requested
        file.grow(additional_slots)?;
        let curr_length = file.length()?; // we must read the updated (grown) length
        let total_slots = curr_length / Self::SLOT_SIZE;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock` guarantees that the
        // first caller sets the value and all subsequent calls reuse it
        let _ = MID.get_or_init(|| MODULE_ID);

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, cfg.flush_duration, curr_length, total_slots));

        // INFO: we spawn the thread for background sync
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self {
            core,
            tx: Some(tx),
            _t: core::marker::PhantomData,
        })
    }

    /// Create/open a new [`FrozenFile`] instance
    fn open_file(path: std::path::PathBuf, cfg: &FMCfg) -> FrozenRes<(FrozenFile, usize)> {
        let ff_cfg = FFCfg {
            path,
            chunk_size: Self::SLOT_SIZE,
            initial_chunk_amount: cfg.initial_count,
        };

        let file = FrozenFile::new::<MODULE_ID>(ff_cfg)?;
        let curr_length = file.length()?;

        Ok((file, curr_length))
    }

    #[inline]
    fn validate_t() -> FrozenRes<()> {
        if std::mem::needs_drop::<T>() {
            return new_err_default(err::DRP);
        }

        let align = std::mem::align_of::<T>();
        if align != 8 {
            return new_err_default(err::ALN);
        }

        let size = std::mem::size_of::<T>();
        if size == 0 {
            return new_err_default(err::ZRO);
        }

        if size % 8 != 0 {
            return new_err_default(err::SZE);
        }

        Ok(())
    }

    /// Blocks until given `epoch` becomes durable
    ///
    /// ## Batching
    ///
    /// With respect to `flush_duration`, all write ops are batched before sync, which is executed by flusher tx
    /// working in background, while each write is assigned w/ current durable epoch, and all writes which
    /// observe the exact same epoch, belong to the same durability window, and are all sync'ed together
    ///
    /// When a background sync succeeds, the internal durable epoch is incremented, indicating that all writes
    /// that observed the previous epoch are now durable on disk
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_wait_epoch");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x04,
    ///     flush_duration: std::time::Duration::from_micros(0x60),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg).unwrap();
    ///
    /// let epoch = unsafe { mmap.write(0, |v| *v = 0x8A) }.unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0x8A);
    /// ```
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        if let Some(sync_err) = self.core.get_sync_error() {
            return Err(sync_err);
        }

        let durable_epoch = self.core.durable_epoch.load(atomic::Ordering::Acquire);
        if durable_epoch >= epoch {
            return Ok(());
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(err::LPN, e),
        };

        loop {
            if let Some(sync_err) = self.core.get_sync_error() {
                return Err(sync_err);
            }

            if self.core.durable_epoch.load(atomic::Ordering::Acquire) >= epoch {
                return Ok(());
            }

            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(err::LPN, e),
            };
        }
    }

    /// Read a `T` at given `index` via callback (`f`)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_read_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(0x60),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg).unwrap();
    ///
    /// let epoch = unsafe { mmap.write(0, |v| *v = 0x0A) }.unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0x0A);
    /// ```
    #[inline(always)]
    pub unsafe fn read<R>(&self, index: usize, f: impl FnOnce(*const T) -> R) -> FrozenRes<R> {
        let offset = Self::SLOT_SIZE * index;

        let _guard = self.core.acquire_io_lock()?;
        let _lock = self.core.locks.lock(index);

        let ptr = unsafe { self.core.map.as_ptr(offset) };
        Ok(f(ptr))
    }

    /// Write/update a `T` at given `index` via callback (`f`)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_write_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg).unwrap();
    ///
    /// let epoch = unsafe {mmap.write(1, |v| *v = 0x2B) }.unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = unsafe { mmap.read(1, |v| *v) }.unwrap();
    /// assert_eq!(val, 0x2B);
    /// ```
    #[inline(always)]
    pub unsafe fn write(&self, index: usize, f: impl FnOnce(*mut T)) -> FrozenRes<TEpoch> {
        // propagate prev errors
        if let Some(err) = self.core.get_sync_error() {
            return Err(err);
        }

        let offset = Self::SLOT_SIZE * index;

        let _guard = self.core.acquire_io_lock()?;
        let _lock = self.core.locks.lock(index);

        let ptr = unsafe { self.core.map.as_mut_ptr(offset) };
        f(ptr);

        self.core.dirty.store(true, atomic::Ordering::Release);
        let epoch = self.core.incr_curr_epoch();

        Ok(epoch)
    }

    /// Write/update a `T` at given `index` via callback (`f`) w/ instant durability
    ///
    /// This function performs a blocking hard-sync, unlike [`FrozenMMap::write`], the update is immediately
    /// persisted to the underlying storage device
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_write_sync");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg).unwrap();
    /// unsafe { mmap.write_sync(0, |v| *v = 0xC0DE) }.unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0xC0DE);
    /// ```
    #[inline(always)]
    pub unsafe fn write_sync(&self, index: usize, f: impl FnOnce(*mut T)) -> FrozenRes<()> {
        // propagate prev errors
        if let Some(err) = self.core.get_sync_error() {
            return Err(err);
        }

        let offset = Self::SLOT_SIZE * index;

        // block flush_tx scheduling
        let _flush_guard = self.core.lock.lock().map_err(|e| new_err_raw(err::LPN, e))?;

        // we use exlusive lock as we perform blocking hard sync
        let _guard = self.core.acquire_exclusive_io_lock()?;

        let _lock = self.core.locks.lock(index);
        let ptr = unsafe { self.core.map.as_mut_ptr(offset) };
        f(ptr);

        // blocking hard sync
        self.core.sync()?;

        // NOTE: we hard sync we flushed an entier batch, so we can skip the sync via flush_tx as the
        // current batch is durable

        self.core.mark_epoch_durable();
        let prev = self.core.dirty.swap(false, atomic::Ordering::AcqRel);

        // NOTE: we must also notify cv's waiting for durability (we skip if there was no batch to sync)
        if prev {
            let _g = self.core.durable_lock.lock().map_err(|e| new_err_raw(err::LPN, e))?;
            self.core.durable_cv.notify_all();
        }

        Ok(())
    }

    /// Read current available count of slots, where each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`]
    ///
    /// ## Working
    ///
    /// This call performs a syscall to fetch current length of [`FrozenFile`] from fs, as the current length of the
    /// file is not cached anywhere in the pipeline to avoid TOCTAU race conditions
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_grow_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg.clone()).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x02);
    ///
    /// drop(mmap);
    ///
    /// let mmap = FrozenMMap::<u64, MODULE_ID>::new_grown(&path, cfg, 0x03).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x02 + 0x03);
    /// ```
    #[inline]
    pub fn total_slots(&self) -> usize {
        self.core.curr_length / Self::SLOT_SIZE
    }

    /// Delete the underlying [`FrozenFile`] used for [`FrozenMMap`] from fs
    ///
    /// ## Working
    ///
    /// When `delete` is called, all read, write, and (background) sync ops are paused (indefinitely),
    /// whule deletion is done with following steps:
    ///
    /// - acquire an exclusive `io_lock` (all other ops are paused indefinitely)
    /// - if any batch is pending for sync,
    ///   - swap the flag
    ///   - call sync manually
    ///   - incr epoch and update cv
    /// - brodcast closing so flusher tx could wrap up
    /// - `munmap(2)` current mapping
    /// - call delete on [`FrozenFile`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_delete_mmap");
    ///
    /// let cfg = FMCfg {
    ///     initial_count: 0x04,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mut mmap = FrozenMMap::<u64, MODULE_ID>::new(&path, cfg).unwrap();
    /// mmap.delete().unwrap();
    /// assert!(!path.exists());
    /// ```
    pub fn delete(&mut self) -> FrozenRes<()> {
        let core = &self.core;

        // pause all read, write and bg sync ops while growing
        let _lock = core.acquire_exclusive_io_lock()?;

        // swap dirty flag and brodcast closing
        if core.dirty.swap(false, atomic::Ordering::AcqRel) {
            self.core.closed.store(true, atomic::Ordering::Release);
            let _g = core.durable_lock.lock().map_err(|e| new_err_raw(err::LPN, e))?;
            core.durable_cv.notify_all();
        }

        // NOTE: we must broadcast that the close is happening to allow flusher tx to wrap up
        core.closed.store(true, atomic::Ordering::Release);
        core.cv.notify_one();

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        self.munmap()?;
        core.file.delete()
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        let length = self.core.curr_length;
        unsafe { self.core.map.unmap(length) }
    }
}

impl<T, const MODULE_ID: u8> Drop for FrozenMMap<T, MODULE_ID>
where
    T: Sized + Send + Sync,
{
    fn drop(&mut self) {
        let is_closed = self.core.closed.swap(true, atomic::Ordering::Release);
        self.core.cv.notify_one(); // notify flusher tx to shut

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        // we must acquire an exclusive lock, to prevent dropping while sync, growing or any io ops
        let _io_lock = self.core.acquire_exclusive_io_lock();

        // free up the boxed error (if any)
        let ptr = self.core.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }

        if !is_closed {
            let _ = self.munmap();
        }
    }
}

impl<T, const MODULE_ID: u8> fmt::Display for FrozenMMap<T, MODULE_ID>
where
    T: Sized + Send + Sync,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{fd: {}, total_slots: {}, len: {}}}",
            self.core.file.fd(),
            self.total_slots(),
            self.core.curr_length,
        )
    }
}

#[derive(Debug)]
struct Core {
    map: TMap,
    locks: Locks,
    file: FrozenFile,
    cv: sync::Condvar,
    curr_length: usize,
    lock: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    dirty: atomic::AtomicBool,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    flush_duration: time::Duration,
    current_epoch: atomic::AtomicU64,
    durable_epoch: atomic::AtomicU64,
    error: atomic::AtomicPtr<FrozenErr>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(
        map: TMap,
        file: FrozenFile,
        flush_duration: time::Duration,
        curr_length: usize,
        total_slots: usize,
    ) -> Self {
        Self {
            map,
            file,
            curr_length,
            flush_duration,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            locks: Locks::new(total_slots),
            durable_cv: sync::Condvar::new(),
            durable_lock: sync::Mutex::new(()),
            dirty: atomic::AtomicBool::new(false),
            closed: atomic::AtomicBool::new(false),
            current_epoch: atomic::AtomicU64::new(0),
            durable_epoch: atomic::AtomicU64::new(0),
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        unsafe { self.map.sync(self.curr_length) }?;
        self.file.sync()
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

    #[inline(always)]
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
    fn acquire_io_lock(&self) -> FrozenRes<sync::RwLockReadGuard<'_, ()>> {
        self.io_lock.read().map_err(|e| new_err_raw(err::LPN, e))
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> FrozenRes<sync::RwLockWriteGuard<'_, ()>> {
        self.io_lock.write().map_err(|e| new_err_raw(err::LPN, e))
    }

    #[inline]
    fn incr_curr_epoch(&self) -> u64 {
        self.current_epoch.fetch_add(1, atomic::Ordering::Release) + 1
    }

    #[inline]
    fn mark_epoch_durable(&self) {
        let curr_epoch = self.current_epoch.load(atomic::Ordering::Acquire);
        self.durable_epoch.store(curr_epoch, atomic::Ordering::Release);
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<thread::JoinHandle<()>> {
        match thread::Builder::new()
            .name("fm-flush-tx".into())
            .spawn(move || Self::flush_tx(core))
        {
            Ok(tx) => Ok(tx),
            Err(error) => new_err(err::FXE, error),
        }
    }

    fn flush_tx(core: sync::Arc<Self>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(error) => {
                core.set_sync_error(new_err_raw(err::FXE, error));
                core.cv.notify_all();
                return;
            }
        };

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(err::TXE, e));
                    core.cv.notify_all();
                    return;
                }
            };

            // NOTE: we must read values of close brodcast before acquire exclusive lock,
            // if done otherwise, we impose serious deadlock sort of situation for the the flusher tx

            let dirty = core.dirty.swap(false, atomic::Ordering::AcqRel);
            let closing = core.closed.load(atomic::Ordering::Acquire);

            if !dirty {
                if closing {
                    core.cv.notify_all();
                    return;
                }

                continue;
            }

            // INFO: we must acquire an exclusive IO lock for sync, hence no write, read or
            // grow could kick in while sync is in progress

            let io_lock = match core.acquire_exclusive_io_lock() {
                Ok(lock) => lock,
                Err(e) => {
                    core.set_sync_error(e);
                    core.cv.notify_all();
                    return;
                }
            };

            // INFO: we must drop the guard before syscall, as its a blocking operation and holding
            // the mutex while the syscall takes place is not a good idea, while we drop the mutex
            // and acqurie it again, in-between other process could acquire it and use it
            drop(guard);

            // NOTE: We snapshot `current_epoch` before sync to establish a strict batch boundary, all writes
            // up to `target_epoch` are guaranteed to be part of this flush window, while anything beyound belongs
            // to the next batch
            let target_epoch = core.current_epoch.load(atomic::Ordering::Acquire);

            // NOTE:
            //
            // - if sync fails, we update the Core::error w/ the received error object
            // - we clear it up when another sync call succeeds
            // - this is valid, as the underlying sync flushes entire mmaped region, hence
            //   even if the last call failed, and the new one succeeded, we do get the durability
            //   guarenty for the old data as well

            match core.sync() {
                Ok(_) => {
                    core.durable_epoch.store(target_epoch, atomic::Ordering::Release);

                    let _g = match core.durable_lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(err::LPN, e));
                            return;
                        }
                    };

                    core.clear_sync_error();
                    core.durable_cv.notify_all();
                }
                Err(err) => {
                    core.set_sync_error(err);
                    core.durable_cv.notify_all();
                }
            }

            drop(io_lock);
            guard = match core.lock.lock() {
                Ok(g) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(err::LPN, e));
                    core.durable_cv.notify_all();
                    return;
                }
            };
        }
    }
}

#[derive(Debug)]
struct Locks(Box<[atomic::AtomicU8]>);

impl Locks {
    const LOCK: u8 = 1;
    const UNLOCK: u8 = 0;

    const L1_CONTENTION: usize = 0x10;
    const L2_CONTENTION: usize = 0x20;

    fn new(cap: usize) -> Self {
        let mut slots = Vec::with_capacity(cap);
        for _ in 0..cap {
            slots.push(atomic::AtomicU8::new(Self::UNLOCK));
        }

        Self(slots.into_boxed_slice())
    }

    #[inline(always)]
    fn lock(&self, index: usize) -> LockGuard<'_> {
        let val = &self.0[index];
        let mut spins = 0;

        loop {
            if val
                .compare_exchange_weak(
                    Self::UNLOCK,
                    Self::LOCK,
                    atomic::Ordering::Acquire,
                    atomic::Ordering::Relaxed,
                )
                .is_ok()
            {
                return LockGuard(val);
            }

            // we must backoff under contention

            // NOTE:
            //
            // We have three levels of backoff,
            //
            // 1. Busy waiting w/ CPU hint
            // 2. Willingly allow preemption by OS schedular
            // 3. Sleep the thread (increasing w/ exponenial factor)

            if hints::likely(spins < Self::L1_CONTENTION) {
                std::hint::spin_loop();
            } else if spins < Self::L2_CONTENTION {
                thread::yield_now();
            } else {
                let ns = 0x30 << (spins - Self::L2_CONTENTION).min(0x0A);
                thread::sleep(time::Duration::from_nanos(ns));
            }

            spins += 1;
        }
    }
}

struct LockGuard<'a>(&'a atomic::AtomicU8);

impl Drop for LockGuard<'_> {
    fn drop(&mut self) {
        self.0.store(Locks::UNLOCK, atomic::Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // NOTE: we keep this small on purpose, so we won't have to wait at all in tests
    const FLUSH_DURATION: time::Duration = time::Duration::from_micros(10);

    const MID: u8 = 0;
    const INIT_SLOTS: usize = 0x0A;

    fn new_tmp() -> (tempfile::TempDir, std::path::PathBuf, FMCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_map");

        let cfg = FMCfg {
            initial_count: INIT_SLOTS,
            flush_duration: FLUSH_DURATION,
        };

        (dir, path, cfg)
    }

    mod fm_lifecycle {
        use super::*;

        #[test]
        fn ok_new() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            assert_eq!(mmap.core.flush_duration, FLUSH_DURATION);
            assert!(!mmap.core.dirty.load(atomic::Ordering::Acquire));
            assert!(!mmap.core.closed.load(atomic::Ordering::Acquire));
            assert_eq!(mmap.core.durable_epoch.load(atomic::Ordering::Acquire), 0);
            assert_eq!(mmap.core.curr_length, INIT_SLOTS * FrozenMMap::<u64, MID>::SLOT_SIZE);

            // satisfies the bg thread was spawned correctly
            assert!(mmap.core.error.load(atomic::Ordering::Acquire).is_null());

            // satisfies wait on epoch works
            let epoch = unsafe { mmap.write(0, |f| *f = 0x0A).unwrap() };
            assert!(mmap.wait_for_durability(epoch).is_ok());
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, path, cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            drop(mmap1);

            // open existing
            let mmap2 = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();
            drop(mmap2);
        }

        #[test]
        fn err_new_when_change_in_cfg() {
            let (_dir, path, mut cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            drop(mmap1);

            // update cfg + opne existing
            cfg.initial_count = INIT_SLOTS * 2;
            assert!(FrozenMMap::<u64, MID>::new(path, cfg).is_err());
        }

        #[test]
        fn ok_delete() {
            let (_dir, path, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.file.exists().unwrap());
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, path, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.file.exists().unwrap());
            assert!(mmap.delete().is_err());
        }

        #[test]
        fn ok_drop_persists_when_dropped_before_bg_flush() {
            let (_dir, path, cfg) = new_tmp();
            const VAL: u64 = 0x0A;

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |byte| *byte = VAL).unwrap() };
                drop(mmap);
            }

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                let val = unsafe { mmap.read(0, |byte| *byte).unwrap() };
                assert_eq!(val, VAL);
            }
        }
    }

    mod fm_validate_t {
        use super::*;

        #[repr(C, align(8))]
        struct OkT {
            a: u64,
            b: u64,
        }

        #[repr(C)]
        struct BadAlignT {
            a: u32,
            b: u32,
        }

        #[repr(C, align(4))]
        struct BadSizeT {
            a: u32,
            b: u16,
        }

        #[repr(C, align(8))]
        struct DropT(u64);

        impl Drop for DropT {
            fn drop(&mut self) {}
        }

        #[repr(C, align(8))]
        struct ZstT;

        #[test]
        fn ok_validate_t() {
            assert!(FrozenMMap::<OkT, MID>::validate_t().is_ok());
        }

        #[test]
        fn err_validate_t_when_drop() {
            assert!(FrozenMMap::<DropT, MID>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_not_8_byte_aligned() {
            assert!(FrozenMMap::<BadAlignT, MID>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_size_not_multiple_of_8() {
            assert!(FrozenMMap::<BadSizeT, MID>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_zero_sized() {
            assert!(FrozenMMap::<ZstT, MID>::validate_t().is_err());
        }

        #[test]
        fn err_new_when_t_implements_drop() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<DropT, MID>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_is_not_8_byte_aligned() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadAlignT, MID>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_size_is_not_multiple_of_8() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadSizeT, MID>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_is_zero_sized() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<ZstT, MID>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_grown_when_t_implements_drop() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<DropT, MID>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_is_not_8_byte_aligned() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadAlignT, MID>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_size_is_not_multiple_of_8() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadSizeT, MID>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_is_zero_sized() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<ZstT, MID>::new_grown(path, cfg, 1).is_err());
        }
    }

    mod fm_new_grown {
        use super::*;

        #[test]
        fn ok_new_grown_updates_length() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS);
            drop(mmap);

            let mmap = FrozenMMap::<u64, MID>::new_grown(path, cfg, 0x0A).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + 0x0A);
            assert_eq!(
                mmap.core.curr_length,
                (INIT_SLOTS + 0x0A) * FrozenMMap::<u64, MID>::SLOT_SIZE
            );
        }

        #[test]
        fn err_new_grown_with_preexisting_instance() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS);

            assert!(FrozenMMap::<u64, MID>::new_grown(path, cfg, 0x0A).is_err());
        }

        #[test]
        fn ok_new_grown_cycle() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            drop(mmap);

            let mmap = FrozenMMap::<u64, MID>::new_grown(&path, cfg.clone(), 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + 0x100);
            drop(mmap);

            let mmap = FrozenMMap::<u64, MID>::new_grown(&path, cfg.clone(), 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + (2 * 0x100));
            drop(mmap);

            let mmap = FrozenMMap::<u64, MID>::new_grown(path, cfg, 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + (3 * 0x100));
        }

        #[test]
        fn ok_write_reopen_grown_read() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |v| *v = 0xAA).unwrap() };
            }

            {
                let mmap = FrozenMMap::<u64, MID>::new_grown(&path, cfg.clone(), 0x10).unwrap();
                unsafe { mmap.write(0, |v| *v = 0xBB).unwrap() };

                let val = unsafe { mmap.read(0, |v| *v).unwrap() };
                assert_eq!(val, 0xBB);
            }
        }

        #[test]
        fn ok_write_reopen_grown_read_cycle() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |v| *v = 1).unwrap() };
            }

            for i in 0..2 {
                let mmap = FrozenMMap::<u64, MID>::new_grown(&path, cfg.clone(), 0x10).unwrap();
                let idx = mmap.total_slots() - 1;
                unsafe { mmap.write(idx, |v| *v = (i + 2) as u64).unwrap() };
                drop(mmap);
            }

            let mmap = FrozenMMap::<u64, MID>::new(&path, cfg).unwrap();

            let base = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(base, 1);

            let last_idx = mmap.total_slots() - 1;
            let last = unsafe { mmap.read(last_idx, |v| *v).unwrap() };
            assert_eq!(last, 3);
        }

        #[test]
        fn err_new_grown_while_previous_instance_is_alive() {
            let (_dir, path, cfg) = new_tmp();

            let _mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
            let reopened = FrozenMMap::<u64, MID>::new_grown(&path, cfg, 0x10);

            assert!(reopened.is_err());
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn ok_write_wait_read_cycle() {
            const VAL: u64 = 0xDEADC0DE;
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            // write + sync
            let epoch = unsafe { mmap.write(0, |ptr| *ptr = VAL).unwrap() };
            mmap.wait_for_durability(epoch).unwrap();

            // read + verify
            let val = unsafe { mmap.read(0, |ptr| *ptr).unwrap() };
            assert_eq!(val, VAL);
        }

        #[test]
        fn ok_write_read_without_wait() {
            const VAL: u64 = 0xDEADC0DE;
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            unsafe { mmap.write(0, |ptr| *ptr = VAL).unwrap() };
            let val = unsafe { mmap.read(0, |ptr| *ptr).unwrap() };
            assert_eq!(val, VAL);
        }
    }

    mod fm_write_sync_read {
        use super::*;

        #[test]
        fn ok_write_sync_read() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            unsafe { mmap.write_sync(0, |v| *v = 0x4C).unwrap() };

            let val = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(val, 0x4C);
        }

        #[test]
        fn ok_write_sync_wait_returns_immediately() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            let _ = unsafe { mmap.write_sync(0, |v| *v = 0x6A).unwrap() };

            let val = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(val, 0x6A);
        }

        #[test]
        fn ok_write_sync_followed_by_async_write() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();
            unsafe { mmap.write_sync(0, |v| *v = 0x0A).unwrap() };

            let epoch = unsafe { mmap.write(0, |v| *v = 0x14).unwrap() };
            mmap.wait_for_durability(epoch).unwrap();

            let val = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(val, 0x14);
        }

        #[test]
        fn ok_write_sync_makes_prev_batch_durable() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            let async_epoch = unsafe { mmap.write(0, |v| *v = 1).unwrap() };
            unsafe { mmap.write_sync(1, |v| *v = 2).unwrap() };
            mmap.wait_for_durability(async_epoch).unwrap();

            let v1 = unsafe { mmap.read(0, |v| *v).unwrap() };
            let v2 = unsafe { mmap.read(1, |v| *v).unwrap() };

            assert_eq!(v1, 1);
            assert_eq!(v2, 2);
        }

        #[test]
        fn ok_write_sync_persists_across_reopen() {
            let (_dir, path, cfg) = new_tmp();
            const VAL: u64 = 0x1000;

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write_sync(0, |v| *v = VAL).unwrap() };
            }

            {
                let mmap = FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap();
                let val = unsafe { mmap.read(0, |v| *v).unwrap() };
                assert_eq!(val, VAL);
            }
        }
    }

    mod fm_durability {
        use super::*;

        #[test]
        fn ok_wait_then_drop() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            let epoch = unsafe { mmap.write(0, |v| *v = 7).unwrap() };
            mmap.wait_for_durability(epoch).unwrap();

            drop(mmap);
        }

        #[test]
        fn ok_epoch_monotonicity() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64, MID>::new(path, cfg).unwrap();

            let e1 = unsafe { mmap.write(0, |v| *v = 1).unwrap() };
            mmap.wait_for_durability(e1).unwrap();

            let e2 = unsafe { mmap.write(0, |v| *v = 2).unwrap() };
            mmap.wait_for_durability(e2).unwrap();
            assert!(e2 >= e1);
        }

        #[test]
        fn ok_wait_for_durability_with_multi_writers() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64, MID>::new(path, cfg).unwrap());

            let mut handles = Vec::new();
            for _ in 0..2 {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    let epoch = unsafe { mmap.write(0, |v| *v += 1).unwrap() };
                    mmap.wait_for_durability(epoch).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let val = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(val, 2);
        }
    }

    mod fm_concurrency {
        use super::*;

        #[test]
        fn ok_parallel_reads_with_diff_index() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64, MID>::new(path, cfg).unwrap());

            unsafe { mmap.write(0, |v| *v = 0x10).unwrap() };
            unsafe { mmap.write(1, |v| *v = 0x20).unwrap() };

            let t1 = {
                let mmap = mmap.clone();
                thread::spawn(move || unsafe { mmap.read(0, |v| *v).unwrap() })
            };

            let t2 = {
                let mmap = mmap.clone();
                thread::spawn(move || unsafe { mmap.read(1, |v| *v).unwrap() })
            };

            assert_eq!(t1.join().unwrap(), 0x10);
            assert_eq!(t2.join().unwrap(), 0x20);
        }

        #[test]
        fn ok_multi_tx_drop_then_reopen_grown() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = sync::Arc::new(FrozenMMap::<u64, MID>::new(&path, cfg.clone()).unwrap());

                let mut handles = Vec::new();
                for i in 0..2u64 {
                    let mmap = mmap.clone();
                    handles.push(thread::spawn(move || {
                        let _ = unsafe { mmap.write(i as usize, |v| *v = i + 1).unwrap() };
                    }));
                }

                for i in 0..2usize {
                    let mmap = mmap.clone();
                    handles.push(thread::spawn(move || {
                        let _ = unsafe { mmap.read(i, |v| *v).unwrap() };
                    }));
                }

                for h in handles {
                    h.join().unwrap();
                }
            }

            {
                let mmap = FrozenMMap::<u64, MID>::new_grown(&path, cfg.clone(), 0x10).unwrap();
                assert_eq!(mmap.total_slots(), INIT_SLOTS + 0x10);

                for i in 0..2u64 {
                    let val = unsafe { mmap.read(i as usize, |v| *v).unwrap() };
                    assert_eq!(val, i + 1);
                }

                let idx = mmap.total_slots() - 1;
                unsafe { mmap.write(idx, |v| *v = 0xDEAD).unwrap() };

                let val = unsafe { mmap.read(idx, |v| *v).unwrap() };
                assert_eq!(val, 0xDEAD);
            }
        }
    }
}
