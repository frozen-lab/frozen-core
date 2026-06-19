//! Custom implementation of `mmap(2)`
//!
//! ## Constraints
//!
//! [`FrozenMMap`] treats the mapped file as raw storage for values of `T`. Because of that,
//! `T` must be a POD type which is safe to persist and later reinterpret from bytes.
//!
//! Required properties for `T`,
//!
//! - Must use `#[repr(C)]`
//! - Should be 8-bytes aligned
//! - Must not implement [`Drop`]
//! - `size_of::<T>()` should be multiple of `8`
//!
//! *NOTE:* `T` must not contain heap owning or process-local pointers like [`Vec`], [`String`],
//! [`Box`], references and function pointers, or other fields whose bit-pattern is not stable
//! across reopen.
//!
//! These constrains are enforced as [`FrozenMMap`] does not serialize or deserialize values. It
//! directly reads and writes `T` inside a memory mapped file. That means `T` must have a stable
//! layout and must remain valid when the file is reopened in a later process.
//!
//! ## Example
//!
//! ```
//! use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
//!
//! const MODULE_ID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_mmap");
//!
//! let cfg = FrozenMMapCfg {
//!     module_id: MODULE_ID,
//!     initial_count: 0x0A,
//!     immediate_durability: false,
//!     flush_duration: std::time::Duration::from_micros(0x96),
//! };
//!
//! let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
//! assert_eq!(mmap.total_slots(), 0x0A);
//!
//! let ticket = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
//! let _ = futures::executor::block_on(ticket).unwrap();
//!
//! let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//!
//! drop(mmap);
//!
//! let reopened = FrozenMMap::<u64>::new_grown(&path, cfg, 0x05).unwrap();
//! assert_eq!(reopened.total_slots(), 0x0A + 0x05);
//!
//! let val = unsafe { reopened.read(0, |v| *v) }.unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    ack,
    error::FrozenResult,
    ffile::{FrozenFile, FrozenFileCfg},
    hints,
};
use std::{
    fmt,
    sync::{self, atomic},
    thread, time,
};

/// type for `epoch` used by write ops
pub type TEpoch = u64;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// Error codes for [`FrozenMMap`]
pub(in crate::fmmap) mod err {
    use crate::error::{ErrCode, FrozenError, FrozenResult};

    /// Domain Id for [`FrozenMMap`] is **18**
    const ERRDOMAIN: u8 = 0x12;

    /// module id used for [`FrozenMMap`]
    pub static MID: std::sync::OnceLock<u8> = std::sync::OnceLock::new();

    #[cfg(not(test))]
    #[inline(always)]
    pub fn mid() -> &'static u8 {
        MID.get().unwrap()
    }

    #[cfg(test)]
    #[inline(always)]
    pub fn mid() -> &'static u8 {
        MID.get_or_init(|| 0)
    }

    /// internal fuck up (hault and catch fire)
    pub const HCF: ErrCode = ErrCode::new(0x02, "hault and catch fire");

    /// unknown error (fallback)
    pub const UNK: ErrCode = ErrCode::new(0x04, "unknown error");

    /// no more memory available
    pub const NMM: ErrCode = ErrCode::new(0x06, "not enough memory available on the device");

    /// syncing error
    pub const SYN: ErrCode = ErrCode::new(0x08, "failed to sync/flush data to storage device");

    /// no write/read perm
    pub const PRM: ErrCode = ErrCode::new(0x0A, "missing permissions for IO");

    /// type `T` must not be zero sized
    pub const ZRO: ErrCode = ErrCode::new(0x0C, "type T must not be zero sized");

    /// flush_tx error (unable to spawn)
    pub const FXE: ErrCode = ErrCode::new(0x10, "unable to spawn flush_tx");

    /// type `T` implements drop
    pub const DRP: ErrCode = ErrCode::new(0x12, "type T must not implement `Drop`");

    /// type `T` is not 8 bytes aligned
    pub const ALN: ErrCode = ErrCode::new(0x14, "type T must be 8-bytes aligned");

    /// `size_of::<T>()` is not multiple of 8
    pub const SZE: ErrCode = ErrCode::new(0x16, "`size_of::<T>()` must be multiple of 8 bytes");

    #[inline]
    pub(in crate::fmmap) fn new_err<R, E: std::fmt::Display>(
        code: ErrCode,
        error: E,
    ) -> FrozenResult<R> {
        let err = FrozenError::new_raw(*mid(), ERRDOMAIN, code, error);
        Err(err)
    }

    #[inline]
    pub(in crate::fmmap) fn new_err_default<R>(code: ErrCode) -> FrozenResult<R> {
        let err = FrozenError::new_raw(*mid(), ERRDOMAIN, code, "");
        Err(err)
    }
}

/// Config for [`FrozenMMap`]
#[derive(Debug, Clone)]
pub struct FrozenMMapCfg {
    /// Identifier used for error propagation by [`frozen_core::error::FrozenError`]
    pub module_id: u8,

    /// Number of slots to pre-allocate when [`FrozenMMap`] is initialized
    ///
    /// Each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`], where initial file length will
    /// be `chunk_size * initial_count` (bytes)
    pub initial_count: usize,

    /// Time interval used by flusher tx, to batch write ops into a durable window and sync them
    /// together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,

    /// Enables immediate durability scheduing write operations
    ///
    /// When disabled, durability is driven by the background flusher thread with respect to
    /// [`FrozenMMapCfg::flush_duration`] time interval, allowing multiple write calls to be
    /// bathced and flushed together into a single sync operation, reducing strain on resources.
    ///
    /// When enabled, every successful [`FrozenMMap::write`] and [`FrozenMMapTransaction::commit`]
    /// immediately wakes the background flusher thread, disregarding the
    /// [`FrozenMMapCfg::flush_duration`] time interval.
    ///
    /// This configuration is intended for workloads where writes are rare and durability latency
    /// is preferred over batching efficiency.
    pub immediate_durability: bool,
}

/// Custom implementation of `mmap(2)`
///
/// ## Constraints
///
/// [`FrozenMMap`] treats the mapped file as raw storage for values of `T`. Because of that, `T`
/// must be a POD type which is safe to persist and later reinterpret from bytes.
///
/// Required properties for `T`,
///
/// - Must use `#[repr(C)]`
/// - Should be 8-bytes aligned
/// - Must not implement [`Drop`]
/// - `size_of::<T>()` should be multiple of `8`
///
/// *NOTE:* `T` must not contain heap owning or process-local pointers like [`Vec`], [`String`],
/// [`Box`], references and function pointers, or other fields whose bit-pattern is not stable
/// across reopen.
///
/// These constrains are enforced as [`FrozenMMap`] does not serialize or deserialize values. It
/// directly reads and writes `T` inside a memory mapped file. That means `T` must have a stable
/// layout and must remain valid when the file is reopened in a later process.
///
/// ## Example
///
/// ```
/// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
///
/// const MODULE_ID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_mmap");
///
/// let cfg = FrozenMMapCfg {
///     module_id: MODULE_ID,
///     initial_count: 0x0A,
///     immediate_durability: false,
///     flush_duration: std::time::Duration::from_micros(0x96),
/// };
///
/// let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
/// assert_eq!(mmap.total_slots(), 0x0A);
///
/// let ticket = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
/// let _ = futures::executor::block_on(ticket).unwrap();
///
/// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
/// assert_eq!(val, 0xDEADC0DE);
///
/// drop(mmap);
///
/// let reopened = FrozenMMap::<u64>::new_grown(&path, cfg, 0x05).unwrap();
/// assert_eq!(reopened.total_slots(), 0x0A + 0x05);
///
/// let val = unsafe { reopened.read(0, |v| *v) }.unwrap();
/// assert_eq!(val, 0xDEADC0DE);
/// ```
#[derive(Debug)]
pub struct FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    core: sync::Arc<Core>,
    flush_tx_handle: Option<thread::JoinHandle<()>>,
    _t: core::marker::PhantomData<T>,
}

unsafe impl<T> Send for FrozenMMap<T> where T: Sized + Send + Sync {}
unsafe impl<T> Sync for FrozenMMap<T> where T: Sized + Send + Sync {}

impl<T> FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    /// Memory space required for each slot of [`T`] in [`FrozenMMap`]
    pub const SLOT_SIZE: usize = std::mem::size_of::<T>();

    /// Create a new [`FrozenMMap`] instance w/ given [`FrozenMMapCfg`]
    ///
    /// ## Multiple Instances
    ///
    /// For each [`FrozenMMap`] instance, we acquire an exclusive lock from the kernal for the
    /// underlying [`FrozenFile`], when trying to create multiple instances of [`FrozenMMap`], an
    /// error will be thrown.
    ///
    /// ## Capacity Growth
    ///
    /// [`FrozenMMap`] does not support in-place growth of a live mapping, to increase capacity,
    /// drop the current instance and reopen w/ [`FrozenMMap::open_grown`] which provides memory
    /// mapping over grown capacity.
    ///
    /// ## [`FrozenMMapCfg`]
    ///
    /// All configs for [`FrozenMMap`] are stored in [`FrozenMMapCfg`]
    ///
    /// ## Working
    ///
    /// We first create a new [`FrozenFile`] if note already, then map the entire file using
    /// `mmap(2)`, the entire file must read/write `T`, which also should stay constant for the
    /// entire lifetime of file.
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`],
    /// which is used under the hood, one must use config stores like [`Rta`](https://crates.io/crates/rta)
    /// to store config.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x0A,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x0A);
    ///
    /// let ticket = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0xDEADC0DE);
    /// ```
    pub fn new<P: AsRef<std::path::Path>>(path: P, cfg: FrozenMMapCfg) -> FrozenResult<Self> {
        Self::validate_t()?;
        let (file, curr_length) = Self::open_file(path.as_ref().to_path_buf(), &cfg)?;
        let total_slots = curr_length / Self::SLOT_SIZE;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock`
        // guarantees that the first caller sets the value and all subsequent calls reuse it
        let _ = err::MID.get_or_init(|| cfg.module_id);

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, curr_length, total_slots));

        let cloned_core = sync::Arc::clone(&core);
        let flush_tx_handle = match thread::Builder::new()
            .name(format!("mod{}_fmmap_flush_tx", cfg.module_id))
            .spawn(move || bg_flush_thread(cloned_core, cfg.flush_duration))
        {
            Ok(handle) => Some(handle),
            Err(observed_error) => {
                return err::new_err(err::FXE, observed_error);
            }
        };

        Ok(Self { core, flush_tx_handle, _t: core::marker::PhantomData })
    }

    /// Create a new [`FrozenMMap`] instance w/ given [`FrozenMMapCfg`], while growing the
    /// underlying [`FrozenFile`] by `additional_slots` before creating memory mapping
    ///
    /// ## Multiple Instances
    ///
    /// For each [`FrozenMMap`] instance, we acquire an exclusive lock from the kernal for the
    /// underlying [`FrozenFile`], when trying to create multiple instances of [`FrozenMMap`], an
    /// error will be thrown.
    ///
    /// ## Why not create a [`FrozenMMap::grow`] call?
    ///
    /// Previously when [`FrozenMMap::grow`] was attempted, it was observed that, resizing an active
    /// memory mapping in place is tricky in concurrent code, as some threads would still hold
    /// stale/unmapped pointers to mmap due to preemption from the OS schedular
    ///
    /// So, instead of remmaping a live instance, the current API performs growth during open,
    /// making capacity expansion an explicit lifecycle operation, and not a side effect on a live
    /// instance.
    ///
    /// ## [`FrozenMMapCfg`]
    ///
    /// All configs for [`FrozenMMap`] are stored in [`FrozenMMapCfg`]
    ///
    /// ## Working
    ///
    /// We first create a new [`FrozenFile`] if note already, then we grow the file using
    /// [`FrozenFile::grow`] then map the entire file using `mmap(2)`, the entire file must
    /// read/write `T`, which also should stay constant for the entire lifetime of file.
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`],
    /// which is used under the hood, one must use config stores like
    /// [`Rta`](https://crates.io/crates/rta) to store config.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x0A,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x0A).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x0A * 2);
    ///
    /// let ticket = unsafe { mmap.write(0, |v| *v = 0xDEADC0DE) }.unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0xDEADC0DE);
    /// ```
    pub fn new_grown<P: AsRef<std::path::Path>>(
        path: P,
        cfg: FrozenMMapCfg,
        additional_slots: usize,
    ) -> FrozenResult<Self> {
        Self::validate_t()?;
        let (file, _) = Self::open_file(path.as_ref().to_path_buf(), &cfg)?;

        // we grow the underlying FrozenFile as requested
        file.grow(additional_slots)?;
        let curr_length = file.length()?; // we must read the updated (grown) length
        let total_slots = curr_length / Self::SLOT_SIZE;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock`
        // guarantees that the first caller sets the value and all subsequent calls reuse it
        let _ = err::MID.get_or_init(|| cfg.module_id);

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, curr_length, total_slots));

        let cloned_core = sync::Arc::clone(&core);
        let flush_tx_handle = match thread::Builder::new()
            .name(format!("mod{}_fmmap_flush_tx", cfg.module_id))
            .spawn(move || bg_flush_thread(cloned_core, cfg.flush_duration))
        {
            Ok(handle) => Some(handle),
            Err(observed_error) => {
                return err::new_err(err::FXE, observed_error);
            }
        };

        Ok(Self { core, flush_tx_handle, _t: core::marker::PhantomData })
    }

    /// Create/open a new [`FrozenFile`] instance
    fn open_file(
        path: std::path::PathBuf,
        cfg: &FrozenMMapCfg,
    ) -> FrozenResult<(FrozenFile, usize)> {
        let ff_cfg = FrozenFileCfg {
            path,
            module_id: cfg.module_id,
            buffer_size: Self::SLOT_SIZE,
            initial_available_buffers: cfg.initial_count,
        };

        let file = FrozenFile::new(ff_cfg)?;
        let curr_length = file.length()?;

        Ok((file, curr_length))
    }

    #[inline]
    fn validate_t() -> FrozenResult<()> {
        if std::mem::needs_drop::<T>() {
            return err::new_err_default(err::DRP);
        }

        let align = std::mem::align_of::<T>();
        if align != 8 {
            return err::new_err_default(err::ALN);
        }

        let size = std::mem::size_of::<T>();
        if size == 0 {
            return err::new_err_default(err::ZRO);
        }

        if size % 8 != 0 {
            return err::new_err_default(err::SZE);
        }

        Ok(())
    }

    /// Read a `T` at given `index` via callback (`f`)
    ///
    /// ## Concurrency
    ///
    /// Internally, [`FrozenMMap`] implements per-slot locking, so concurrent reads and writes for
    /// at same index is atomic and thread safe, while operations on different indices may proceed
    /// fully in parallel
    ///
    /// ## Safety
    ///
    /// The caller must ensure following:
    ///
    /// - given `index` is within bounds
    /// - underlying memory contains a valid instance of `T`
    /// - provided callback `f` must not,
    ///   - write through the pointer
    ///   - store or leak pointer beyound there lifetime
    ///
    /// Violating any of the above may result in undefined behavior
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_read_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x02,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x60),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let ticket = unsafe { mmap.write(0, |v| *v = 0x0A) }.unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let val = unsafe { mmap.read(0, |v| *v) }.unwrap();
    /// assert_eq!(val, 0x0A);
    /// ```
    #[inline(always)]
    pub unsafe fn read<R>(&self, index: usize, f: impl FnOnce(*const T) -> R) -> FrozenResult<R> {
        let offset = Self::SLOT_SIZE * index;
        let _lock = self.core.locks.lock(index);

        // NOTE: We do avoid acquiring io_lock for read ops to increase the throughput (under the
        // assumption of OS guarantees visibility)

        let ptr = unsafe { self.core.map.as_ptr(offset) };
        Ok(f(ptr))
    }

    /// Write/update a `T` at given `index` via callback (`f`)
    ///
    /// ## Concurrency
    ///
    /// Internally, [`FrozenMMap`] implements per-slot locking, so concurrent reads and writes for
    /// at same index is atomic and thread safe, while operations on different indices may proceed
    /// fully in parallel
    ///
    /// ## Safety
    ///
    /// The caller must ensure following:
    ///
    /// - given `index` is within bounds
    /// - underlying memory contains a valid instance of `T`
    /// - provided callback `f` must not  store or leak pointer beyound there lifetime
    ///
    /// Violating any of the above may result in undefined behavior
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_write_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x02,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let ticket = unsafe {mmap.write(1, |v| *v = 0x2B) }.unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let val = unsafe { mmap.read(1, |v| *v) }.unwrap();
    /// assert_eq!(val, 0x2B);
    /// ```
    #[inline(always)]
    pub unsafe fn write(
        &self,
        index: usize,
        f: impl FnOnce(*mut T),
    ) -> FrozenResult<ack::AckTicket> {
        // propagate prev errors
        if let Some(err) = self.core.completion.get_err() {
            return Err(err);
        }

        let offset = Self::SLOT_SIZE * index;

        let _guard = self.core.acquire_io_lock();
        let _lock = self.core.locks.lock(index);

        let ptr = unsafe { self.core.map.as_mut_ptr(offset) };
        f(ptr);

        self.core.dirty.store(true, atomic::Ordering::Release);
        let epoch = self.core.completion.increment_current_epoch();

        Ok(ack::AckTicket::new(epoch, self.core.completion.clone()))
    }

    /// Read current available count of slots, where each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`]
    ///
    /// ## Working
    ///
    /// This call performs a syscall to fetch current length of [`FrozenFile`] from fs, as the
    /// current length of the file is not cached anywhere in the pipeline to avoid TOCTAU race
    /// conditions
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_grow_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x02,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x02);
    ///
    /// drop(mmap);
    ///
    /// let mmap = FrozenMMap::<u64>::new_grown(&path, cfg, 0x03).unwrap();
    /// assert_eq!(mmap.total_slots(), 0x02 + 0x03);
    /// ```
    #[inline]
    pub fn total_slots(&self) -> usize {
        self.core.curr_length / Self::SLOT_SIZE
    }

    /// Read the total memory footprint (in bytes) used by [`FrozenMMap`]
    ///
    /// *NOTE:* This is an approzimation of memory used, actual RSS may differ depending on paging
    /// and OS
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_mem_usage");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x10,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x60),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let bytes = mmap.memory_usage();
    /// assert!(bytes >= mmap.total_slots() * std::mem::size_of::<u64>());
    /// ```
    #[inline]
    pub fn memory_usage(&self) -> usize {
        // memory of mem-maped region
        let mmap_bytes = self.core.curr_length;

        // memory used for locking
        let lock_bytes = self.core.locks.0.len() * std::mem::size_of::<atomic::AtomicU8>();

        mmap_bytes + lock_bytes
    }

    /// Create a new [`FrozenMMapTransaction`] context for grouping multi write ops into a single atomic
    /// operation
    ///
    /// ## Overview
    ///
    /// The use of [`FrozenMMapTransaction`] allows to group multiple write ops into a single atomic
    /// operation, hence creating a transactional write operation, which gives following guarantees:
    ///
    /// - All write ops succeed together
    /// - Single epoch to track durability of all writes ops
    /// - Same durability guarantee for all the included write ops
    ///
    /// Simply, this preserves atomic durability semantics for multi index updates
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_tx");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x0A,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(50),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let mut tx = mmap.new_tx();
    /// unsafe { tx.write(0, |v| *v = 0x0A) }.unwrap();
    /// unsafe { tx.write(1, |v| *v = 0x14) }.unwrap();
    ///
    /// let ticket = tx.commit().unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
    /// let v1 = unsafe { mmap.read(1, |v| *v).unwrap() };
    ///
    /// assert_eq!((v0, v1), (0x0A, 0x14));
    /// ```
    #[inline]
    pub fn new_tx(&self) -> FrozenMMapTransaction<'_, T> {
        FrozenMMapTransaction { core: &self.core, ops_vec: Vec::new() }
    }

    /// Delete the underlying [`FrozenFile`] used for [`FrozenMMap`] from fs
    ///
    /// ## Working
    ///
    /// When `delete` is called, all read, write, and (background) sync ops are paused
    /// (indefinitely), whule deletion is done with following steps:
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
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_delete_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x04,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mut mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    /// mmap.delete().unwrap();
    /// assert!(!path.exists());
    /// ```
    pub fn delete(&mut self) -> FrozenResult<()> {
        // NOTE: we must broadcast that the close is happening to allow flusher tx to wrap up
        self.core.dirty.store(false, atomic::Ordering::Release);
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.durable_cv.notify_one();

        if let Some(handle) = self.flush_tx_handle.take() {
            let _ = handle.join();
        }

        // pause all new write ops
        let _lock = self.core.acquire_exclusive_io_lock();

        self.munmap()?;
        self.core.file.delete()
    }

    /// Flush the dirty mmap data to persistant storage
    ///
    /// *NOTE:* This call must be paired w/ [`FrozenMMap::flush_file`] for stronger durability
    /// guarantee
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_delete_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x04,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mut mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    /// assert!(unsafe { mmap.flush_mmap() }.is_ok());
    /// ```
    #[inline]
    pub unsafe fn flush_mmap(&self) -> FrozenResult<()> {
        self.core.map.sync(self.core.curr_length)
    }

    /// Perform hard flush for the dirty mmap'ed data for stronger durability guarantee
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_delete_mmap");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x04,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(0x96),
    /// };
    ///
    /// let mut mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    /// assert!(unsafe { mmap.flush_file() }.is_ok());
    /// ```
    #[inline]
    pub unsafe fn flush_file(&self) -> FrozenResult<()> {
        self.core.file.sync()
    }

    #[inline]
    fn munmap(&self) -> FrozenResult<()> {
        let length = self.core.curr_length;
        unsafe { self.core.map.unmap(length) }
    }
}

impl<T> Drop for FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    fn drop(&mut self) {
        let is_closed = self.core.closed.swap(true, atomic::Ordering::Release);
        self.core.cv.notify_one(); // notify flusher tx to shut

        if let Some(handle) = self.flush_tx_handle.take() {
            let _ = handle.join();
        }

        // we must acquire an exclusive lock, to prevent dropping while sync, growing or any io ops
        let _io_lock = self.core.acquire_exclusive_io_lock();

        if !is_closed {
            let _ = self.munmap();
        }
    }
}

impl<T> fmt::Display for FrozenMMap<T>
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

/// ## Why we ignore [`std::sync::PoisonError`]?
///
/// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not
/// protect any mutable state. All the pool invariants and accounting are maintained via atomics
/// and are completely seperated from the mutex.
///
/// A poisoned mutex only indicates that another tx panicked while holding the lock, and indicates
/// an inconsistent state of the protected value. Since no state can be left partially modified
/// under this lock, there is no possible consistency risk to recover from and propagating the
/// poison error would only introduce unnecessary failures into the allocation path.
///
/// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating
/// with the recovered guard.
fn bg_flush_thread(core: sync::Arc<Core>, flush_duration: time::Duration) {
    // init phase (acquiring locks)
    let mut guard = core.lock.lock().unwrap_or_else(|e| e.into_inner());

    // sync loop w/ non-busy waiting
    loop {
        (guard, _) = core.cv.wait_timeout(guard, flush_duration).unwrap_or_else(|e| e.into_inner());

        // NOTE: we must read values of close brodcast before acquire exclusive lock, if done
        // otherwise, we impose serious deadlock sort of situation for the the flusher tx

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

        let io_lock = core.acquire_exclusive_io_lock();

        // INFO: we must drop the guard before syscall, as its a blocking operation and holding
        // the mutex while the syscall takes place is not a good idea, while we drop the mutex
        // and acqurie it again, in-between other process could acquire it and use it
        drop(guard);

        // NOTE: We snapshot `current_epoch` before sync to establish a strict batch boundary,
        // all writes up to `target_epoch` are guaranteed to be part of this flush window,
        // while anything beyound belongs to the next batch
        let target_epoch = core.completion.read_current_epoch();

        // NOTE:
        //
        // - if sync fails, we update the Core::error w/ the received error object
        // - we clear it up when another sync call succeeds
        // - this is valid, as the underlying sync flushes entire mmaped region, hence
        //   even if the last call failed, and the new one succeeded, we do get the durability
        //   guarenty for the old data as well

        if let Err(new_error) = core.sync() {
            core.completion.set_err(new_error);
        } else {
            core.completion.mark_epoch_as_durable(target_epoch);
            core.completion.del_err();
        }

        // NOTE: notify all listeners currently waiting for durability progress
        core.completion.notify_all_listeners();

        drop(io_lock);
        guard = core.acquire_lock();
    }
}

/// A context for grouping multi write ops into a single atomic operation
///
/// ## Overview
///
/// Use of [`FrozenMMapTransaction`] allows to group multiple write ops into a single atomic operation.
///
/// - All included writes are applied together
/// - Single epoch is assinged for an entier transaction
/// - Durability guarantee is same for all included write ops
///
/// ## Example
///
/// ```
/// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
///
/// const MODULE_ID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_tx");
///
/// let cfg = FrozenMMapCfg {
///     module_id: MODULE_ID,
///     initial_count: 0x0A,
///     immediate_durability: false,
///     flush_duration: std::time::Duration::from_micros(50),
/// };
///
/// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
///
/// let mut tx = mmap.new_tx();
/// unsafe { tx.write(0, |v| *v = 0x0A) }.unwrap();
/// unsafe { tx.write(1, |v| *v = 0x14) }.unwrap();
/// unsafe { tx.write(2, |v| *v = 0x18) }.unwrap();
///
/// let ticket = tx.commit().unwrap();
/// let _ = futures::executor::block_on(ticket).unwrap();
///
/// let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
/// let v1 = unsafe { mmap.read(1, |v| *v).unwrap() };
/// let v2 = unsafe { mmap.read(2, |v| *v).unwrap() };
///
/// assert_eq!((v0, v1, v2), (0x0A, 0x14, 0x18));
/// ```
pub struct FrozenMMapTransaction<'a, T> {
    core: &'a Core,
    ops_vec: Vec<(usize, Box<dyn FnOnce(*mut T) + 'a>)>,
}

impl<'a, T> FrozenMMapTransaction<'a, T> {
    /// Append a write op into the [`FrozenMMapTransaction`]
    ///
    /// ## Requirements
    ///
    /// Write ops must follow these safety requirements,
    ///
    /// - No duplicate indices
    /// - No out-of-order writes (must be incremental)
    ///
    /// Violating this constraint would result in [`FrozenError`]
    ///
    /// ## Safety
    ///
    /// Same safety requirements as [`FrozenMMap::write`] apply here
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_tx");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x10,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(50),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let mut tx = mmap.new_tx();
    /// unsafe { tx.write(0, |v| *v = 0x0A) }.unwrap();
    /// unsafe { tx.write(1, |v| *v = 0x0B) }.unwrap();
    /// unsafe { tx.write(2, |v| *v = 0x0C) }.unwrap();
    ///
    /// let ticket = tx.commit().unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
    /// let v1 = unsafe { mmap.read(1, |v| *v).unwrap() };
    /// let v2 = unsafe { mmap.read(2, |v| *v).unwrap() };
    ///
    /// assert_eq!((v0, v1, v2), (0x0A, 0x0B, 0x0C));
    /// ```
    #[inline(always)]
    pub unsafe fn write<F>(&mut self, index: usize, f: F) -> FrozenResult<()>
    where
        F: FnOnce(*mut T) + 'a,
    {
        // NOTE:
        //
        // This check prevents a potential footgun! For a safe transaction all writes must be,
        // - ordered by index (either incr or decr)
        // - no multi writes on same index
        //
        // If any of these is violated, there is a certain risk of deadlock in multi tx env's
        if let Some((last_idx, _)) = self.ops_vec.last() {
            if index <= *last_idx {
                return err::new_err(
                    err::HCF,
                    "tx writes must be strictly ordered, with no more then single ops on given index",
                );
            }
        }

        self.ops_vec.push((index, Box::new(f)));
        Ok(())
    }

    /// Commit the transaction, applying all the writes ops, combined into a single atomic operation
    ///
    /// ## Guarantees
    ///
    /// - All writes are applied under a single epoch
    /// - All writes belong to the same durability batch
    /// - No interleaving with other transactions at epoch level
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FrozenMMapCfg};
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_tx");
    ///
    /// let cfg = FrozenMMapCfg {
    ///     module_id: MODULE_ID,
    ///     initial_count: 0x10,
    ///     immediate_durability: false,
    ///     flush_duration: std::time::Duration::from_micros(50),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();
    ///
    /// let mut tx = mmap.new_tx();
    /// unsafe { tx.write(0, |v| *v = 0x0A) }.unwrap();
    /// unsafe { tx.write(2, |v| *v = 0x0C) }.unwrap();
    ///
    /// let ticket = tx.commit().unwrap();
    /// let _ = futures::executor::block_on(ticket).unwrap();
    ///
    /// let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
    /// let v1 = unsafe { mmap.read(2, |v| *v).unwrap() };
    ///
    /// assert_eq!((v0, v1), (0x0A, 0x0C));
    /// ```
    #[inline(always)]
    pub fn commit(self) -> FrozenResult<ack::AckTicket> {
        if let Some(err) = self.core.completion.get_err() {
            return Err(err);
        }

        let _guard = self.core.acquire_io_lock();

        // NOTE: we must acquire all locks beforehand, to make sure all the write go through
        let mut guards = Vec::with_capacity(self.ops_vec.len());
        for (idx, _) in &self.ops_vec {
            guards.push(self.core.locks.lock(*idx));
        }

        for (idx, op) in self.ops_vec {
            let offset = idx * std::mem::size_of::<T>();
            let ptr = unsafe { self.core.map.as_mut_ptr(offset) };
            op(ptr);
        }

        self.core.dirty.store(true, atomic::Ordering::Release);
        let epoch = self.core.completion.increment_current_epoch();

        Ok(ack::AckTicket::new(epoch, self.core.completion.clone()))
    }
}

#[derive(Debug)]
struct Core {
    completion: sync::Arc<ack::Completion>,
    cv: sync::Condvar,
    curr_length: usize,
    dirty: atomic::AtomicBool,
    io_lock: sync::RwLock<()>,
    map: TMap,
    locks: Locks,
    lock: sync::Mutex<()>,
    file: FrozenFile,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(map: TMap, file: FrozenFile, curr_length: usize, total_slots: usize) -> Self {
        Self {
            map,
            file,
            curr_length,
            completion: sync::Arc::new(ack::Completion::default()),
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            locks: Locks::new(total_slots),
            durable_cv: sync::Condvar::new(),
            dirty: atomic::AtomicBool::new(false),
            closed: atomic::AtomicBool::new(false),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenResult<()> {
        unsafe { self.map.sync(self.curr_length) }?;
        self.file.sync()
    }

    /// NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
    #[inline]
    fn acquire_lock(&self) -> sync::MutexGuard<'_, ()> {
        self.lock.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
    #[inline]
    fn acquire_io_lock(&self) -> sync::RwLockReadGuard<'_, ()> {
        self.io_lock.read().unwrap_or_else(|e| e.into_inner())
    }

    /// NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
    #[inline]
    fn acquire_exclusive_io_lock(&self) -> sync::RwLockWriteGuard<'_, ()> {
        self.io_lock.write().unwrap_or_else(|e| e.into_inner())
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

    const MODULE_ID: u8 = 0;
    const INIT_SLOTS: usize = 0x0A;

    fn new_tmp() -> (tempfile::TempDir, std::path::PathBuf, FrozenMMapCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_map");

        let cfg = FrozenMMapCfg {
            module_id: MODULE_ID,
            initial_count: INIT_SLOTS,
            immediate_durability: false,
            flush_duration: FLUSH_DURATION,
        };

        (dir, path, cfg)
    }

    mod fm_lifecycle {
        use super::*;

        #[test]
        fn ok_new() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            assert!(!mmap.core.dirty.load(atomic::Ordering::Acquire));
            assert!(!mmap.core.closed.load(atomic::Ordering::Acquire));
            assert_eq!(mmap.core.curr_length, INIT_SLOTS * FrozenMMap::<u64>::SLOT_SIZE);

            assert_eq!(mmap.core.completion.read_current_epoch(), 0);
            assert_eq!(mmap.core.completion.read_durable_epoch(), 0);

            // satisfies the bg thread was spawned correctly
            assert!(mmap.core.completion.get_err().is_none());

            // satisfies wait on epoch works
            let ticket = unsafe { mmap.write(0, |f| *f = 0x0A).unwrap() };

            let ticket_epoch = ticket.epoch();
            let durable_epoch = futures::executor::block_on(ticket).unwrap();

            assert!(durable_epoch >= ticket_epoch);
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, path, cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            drop(mmap1);

            // open existing
            let mmap2 = FrozenMMap::<u64>::new(path, cfg).unwrap();
            drop(mmap2);
        }

        #[test]
        fn err_new_when_change_in_cfg() {
            let (_dir, path, mut cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            drop(mmap1);

            // update cfg + opne existing
            cfg.initial_count = INIT_SLOTS * 2;
            assert!(FrozenMMap::<u64>::new(path, cfg).is_err());
        }

        #[test]
        fn ok_delete() {
            let (_dir, path, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.file.exists().unwrap());
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, path, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.file.exists().unwrap());
            assert!(mmap.delete().is_err());
        }

        #[test]
        fn ok_drop_persists_when_dropped_before_bg_flush() {
            let (_dir, path, cfg) = new_tmp();
            const VAL: u64 = 0x0A;

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |byte| *byte = VAL).unwrap() };
                drop(mmap);
            }

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
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
            assert!(FrozenMMap::<OkT>::validate_t().is_ok());
        }

        #[test]
        fn err_validate_t_when_drop() {
            assert!(FrozenMMap::<DropT>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_not_8_byte_aligned() {
            assert!(FrozenMMap::<BadAlignT>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_size_not_multiple_of_8() {
            assert!(FrozenMMap::<BadSizeT>::validate_t().is_err());
        }

        #[test]
        fn err_validate_t_when_zero_sized() {
            assert!(FrozenMMap::<ZstT>::validate_t().is_err());
        }

        #[test]
        fn err_new_when_t_implements_drop() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<DropT>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_is_not_8_byte_aligned() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadAlignT>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_size_is_not_multiple_of_8() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadSizeT>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_when_t_is_zero_sized() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<ZstT>::new(path, cfg).is_err());
        }

        #[test]
        fn err_new_grown_when_t_implements_drop() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<DropT>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_is_not_8_byte_aligned() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadAlignT>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_size_is_not_multiple_of_8() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<BadSizeT>::new_grown(path, cfg, 1).is_err());
        }

        #[test]
        fn err_new_grown_when_t_is_zero_sized() {
            let (_dir, path, cfg) = new_tmp();
            assert!(FrozenMMap::<ZstT>::new_grown(path, cfg, 1).is_err());
        }
    }

    mod fm_new_grown {
        use super::*;

        #[test]
        fn ok_new_grown_updates_length() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS);
            drop(mmap);

            let mmap = FrozenMMap::<u64>::new_grown(path, cfg, 0x0A).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + 0x0A);
            assert_eq!(mmap.core.curr_length, (INIT_SLOTS + 0x0A) * FrozenMMap::<u64>::SLOT_SIZE);
        }

        #[test]
        fn err_new_grown_with_preexisting_instance() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS);

            assert!(FrozenMMap::<u64>::new_grown(path, cfg, 0x0A).is_err());
        }

        #[test]
        fn ok_new_grown_cycle() {
            let (_dir, path, cfg) = new_tmp();

            let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            drop(mmap);

            let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + 0x100);
            drop(mmap);

            let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + (2 * 0x100));
            drop(mmap);

            let mmap = FrozenMMap::<u64>::new_grown(path, cfg, 0x100).unwrap();
            assert_eq!(mmap.total_slots(), INIT_SLOTS + (3 * 0x100));
        }

        #[test]
        fn ok_write_reopen_grown_read() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |v| *v = 0xAA).unwrap() };
            }

            {
                let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x10).unwrap();
                unsafe { mmap.write(0, |v| *v = 0xBB).unwrap() };

                let val = unsafe { mmap.read(0, |v| *v).unwrap() };
                assert_eq!(val, 0xBB);
            }
        }

        #[test]
        fn ok_write_reopen_grown_read_cycle() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
                unsafe { mmap.write(0, |v| *v = 1).unwrap() };
            }

            for i in 0..2 {
                let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x10).unwrap();
                let idx = mmap.total_slots() - 1;
                unsafe { mmap.write(idx, |v| *v = (i + 2) as u64).unwrap() };
                drop(mmap);
            }

            let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();

            let base = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(base, 1);

            let last_idx = mmap.total_slots() - 1;
            let last = unsafe { mmap.read(last_idx, |v| *v).unwrap() };
            assert_eq!(last, 3);
        }

        #[test]
        fn err_new_grown_while_previous_instance_is_alive() {
            let (_dir, path, cfg) = new_tmp();

            let _mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();
            let reopened = FrozenMMap::<u64>::new_grown(&path, cfg, 0x10);

            assert!(reopened.is_err());
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn ok_write_wait_read_cycle() {
            const VAL: u64 = 0xDEADC0DE;
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            // write + sync
            let ticket = unsafe { mmap.write(0, |ptr| *ptr = VAL).unwrap() };

            let ticket_epoch = ticket.epoch();
            let durable_epoch = futures::executor::block_on(ticket).unwrap();

            assert!(durable_epoch >= ticket_epoch);

            // read + verify
            let val = unsafe { mmap.read(0, |ptr| *ptr).unwrap() };
            assert_eq!(val, VAL);
        }

        #[test]
        fn ok_write_read_without_wait() {
            const VAL: u64 = 0xDEADC0DE;
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            unsafe { mmap.write(0, |ptr| *ptr = VAL).unwrap() };
            let val = unsafe { mmap.read(0, |ptr| *ptr).unwrap() };
            assert_eq!(val, VAL);
        }
    }

    mod fm_tx {
        use super::*;

        #[test]
        fn ok_tx_basic_multi_write() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let mut tx = mmap.new_tx();
            unsafe {
                tx.write(0, |v| *v = 1).unwrap();
                tx.write(1, |v| *v = 2).unwrap();
                tx.write(2, |v| *v = 3).unwrap();
            }

            let ticket = tx.commit().unwrap();

            let ticket_epoch = ticket.epoch();
            let durable_epoch = futures::executor::block_on(ticket).unwrap();

            assert!(durable_epoch >= ticket_epoch);

            let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
            let v1 = unsafe { mmap.read(1, |v| *v).unwrap() };
            let v2 = unsafe { mmap.read(2, |v| *v).unwrap() };

            assert_eq!((v0, v1, v2), (1, 2, 3));
        }

        #[test]
        fn ok_tx_single_epoch() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let mut tx = mmap.new_tx();
            unsafe {
                tx.write(0, |v| *v = 0x0A).unwrap();
                tx.write(1, |v| *v = 0x14).unwrap();
            }

            // NOTE: next write must have strictly higher epoch then current one

            let ticket = tx.commit().unwrap();
            let next_ticket = unsafe { mmap.write(2, |v| *v = 0x1E).unwrap() };

            assert!(next_ticket.epoch() > ticket.epoch());
        }

        #[test]
        fn err_tx_out_of_order() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let mut tx = mmap.new_tx();
            unsafe {
                tx.write(2, |v| *v = 1).unwrap();
                let res = tx.write(1, |v| *v = 2);
                assert!(res.is_err());
            }
        }

        #[test]
        fn err_tx_duplicate_index() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let mut tx = mmap.new_tx();
            unsafe {
                tx.write(1, |v| *v = 1).unwrap();
                let res = tx.write(1, |v| *v = 2);
                assert!(res.is_err());
            }
        }

        #[test]
        fn ok_tx_concurrent_non_overlapping() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(path, cfg).unwrap());

            let mut handles = Vec::new();
            for i in 0..2 {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    let mut tx = mmap.new_tx();

                    unsafe {
                        tx.write(i * 2, |v| *v = i as u64).unwrap();
                        tx.write(i * 2 + 1, |v| *v = i as u64).unwrap();
                    }

                    let ticket = tx.commit().unwrap();

                    let ticket_epoch = ticket.epoch();
                    let durable_epoch = futures::executor::block_on(ticket).unwrap();

                    assert!(durable_epoch >= ticket_epoch);
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            for i in 0..2 {
                let v0 = unsafe { mmap.read(i * 2, |v| *v).unwrap() };
                let v1 = unsafe { mmap.read(i * 2 + 1, |v| *v).unwrap() };

                assert_eq!((v0, v1), (i as u64, i as u64));
            }
        }

        #[test]
        fn ok_tx_overwrite_last_wins() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let mut tx = mmap.new_tx();
            unsafe {
                tx.write(0, |v| *v = 1).unwrap();
            }

            tx.commit().unwrap();

            let mut tx2 = mmap.new_tx();
            unsafe {
                tx2.write(0, |v| *v = 2).unwrap();
            }

            let ticket = tx2.commit().unwrap();

            let ticket_epoch = ticket.epoch();
            let durable_epoch = futures::executor::block_on(ticket).unwrap();

            assert!(durable_epoch >= ticket_epoch);

            let val = unsafe { mmap.read(0, |v| *v).unwrap() };
            assert_eq!(val, 2);
        }

        #[test]
        fn ok_tx_persists_across_reopen() {
            let (_dir, path, cfg) = new_tmp();

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap();

                let mut tx = mmap.new_tx();
                unsafe {
                    tx.write(0, |v| *v = 0x3A).unwrap();
                    tx.write(1, |v| *v = 0x54).unwrap();
                }

                let ticket = tx.commit().unwrap();

                let ticket_epoch = ticket.epoch();
                let durable_epoch = futures::executor::block_on(ticket).unwrap();

                assert!(durable_epoch >= ticket_epoch);
            }

            {
                let mmap = FrozenMMap::<u64>::new(&path, cfg).unwrap();

                let v0 = unsafe { mmap.read(0, |v| *v).unwrap() };
                let v1 = unsafe { mmap.read(1, |v| *v).unwrap() };

                assert_eq!((v0, v1), (0x3A, 0x54));
            }
        }
    }

    mod fm_durability {
        use super::*;

        #[test]
        fn ok_wait_then_drop() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let ticket = unsafe { mmap.write(0, |v| *v = 7).unwrap() };

            let ticket_epoch = ticket.epoch();
            let durable_epoch = futures::executor::block_on(ticket).unwrap();

            assert!(durable_epoch >= ticket_epoch);

            drop(mmap);
        }

        #[test]
        fn ok_epoch_monotonicity() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(path, cfg).unwrap();

            let t1 = unsafe { mmap.write(0, |v| *v = 1).unwrap() };
            let t2 = unsafe { mmap.write(0, |v| *v = 2).unwrap() };

            let durable_epoch = futures::executor::block_on(t2).unwrap();
            assert!(durable_epoch >= t1.epoch());
        }

        #[test]
        fn ok_wait_for_durability_with_multi_writers() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(path, cfg).unwrap());

            let mut handles = Vec::new();
            for _ in 0..2 {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    let ticket = unsafe { mmap.write(0, |v| *v += 1).unwrap() };

                    let ticket_epoch = ticket.epoch();
                    let durable_epoch = futures::executor::block_on(ticket).unwrap();

                    assert!(durable_epoch >= ticket_epoch);
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
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(path, cfg).unwrap());

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
                let mmap = sync::Arc::new(FrozenMMap::<u64>::new(&path, cfg.clone()).unwrap());

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
                let mmap = FrozenMMap::<u64>::new_grown(&path, cfg.clone(), 0x10).unwrap();
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

    mod ack_ticket {
        use super::*;

        #[test]
        fn ok_parallel_waiters_same_epoch_window() {
            let (_dir, path, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(path, cfg).unwrap());

            let barrier = sync::Arc::new(sync::Barrier::new(0x10));

            let mut handles = Vec::new();
            for i in 0..0x10usize {
                let mmap = mmap.clone();
                let barrier = barrier.clone();

                handles.push(thread::spawn(move || {
                    barrier.wait();

                    let ticket = unsafe { mmap.write(i % INIT_SLOTS, |v| *v = i as u64).unwrap() };

                    let epoch = ticket.epoch();
                    let durable = futures::executor::block_on(ticket).unwrap();

                    assert!(durable >= epoch);
                }));
            }

            for handle in handles {
                handle.join().expect("worker thread panicked");
            }
        }

        #[test]
        fn ok_parallel_waiters_same_epoch() {
            let completion = sync::Arc::new(ack::Completion::default());

            let mut handles = Vec::new();
            for _ in 0..0x10 {
                let completion = completion.clone();

                handles.push(thread::spawn(move || {
                    let ticket = ack::AckTicket::new(1, completion);

                    assert_eq!(
                        futures::executor::block_on(ticket).expect("ticket must complete"),
                        1
                    );
                }));
            }

            thread::sleep(time::Duration::from_millis(0x0A));

            completion.mark_epoch_as_durable(1);
            completion.notify_all_listeners();

            for handle in handles {
                handle.join().expect("worker thread panicked");
            }
        }
    }
}
