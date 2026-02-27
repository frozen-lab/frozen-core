use super::{new_err, FMMapErrRes, ObjectInterface};
use crate::{error::FrozenRes, hints};
use core::{ffi::CStr, ptr};
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, strerror, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, EOVERFLOW,
    MAP_FAILED, MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

type TPtr = *mut c_void;

/// max allowed retries for `EINTR` errors
const MAX_RETRIES: usize = 0x0A;

/// Custom impl of `mmap(2)` for POSIX systems
#[derive(Debug)]
pub(super) struct POSIXMMap(TPtr);

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] w/ given `fd` and `length`
    pub(super) unsafe fn new(fd: i32, length: size_t) -> FrozenRes<Self> {
        let ptr = mmap_raw(fd, length)?;
        Ok(Self(ptr))
    }

    /// Close [`POSIXMMap`] to give up allocated resources
    pub(super) unsafe fn unmap(&self, length: usize) -> FrozenRes<()> {
        munmap_raw(self.0, length)
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Durability
    ///
    /// In POSIX systems `msync(MS_SYNC)`, does not provide crash safe durability, this syscall is used
    /// as a best-effort operation, to explicitly push dirty mmaped pages into fs writeback
    ///
    /// For strong durability, use of [`FrozenFile::sync`] is required, right after calling [`FrozenMMap::sync`]
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
    /// is guaranteed, so the syscall must be retried
    pub(super) unsafe fn sync(&self, length: usize) -> FrozenRes<()> {
        msync_raw(self.0, length)
    }

    /// Get a mutable (read/write) typed pointer to `T` at given `offset`
    ///
    /// Given `offset` must be aligned w/ `std::mem::size_of::<ObjectInterface<T>>()`
    #[inline]
    pub(super) unsafe fn as_ptr<T>(&self, offset: usize) -> *mut ObjectInterface<T>
    where
        T: Sized + Send + Sync,
    {
        self.0.add(offset) as *mut ObjectInterface<T>
    }
}

/// create a new memory mapping on given `fd` or given `length`
///
/// ## Caveats of `mmap` on POSIX
///
/// In POSIX systems, when calling `mmap()`, the provided offset must be multiple of page size,
/// i.e. `sysconf(_SC_PAGESIZE)`, otherwise an `EINVAL` error is thrown
///
/// For our usecase, we always map an entire file, hence this is never an issue for us
unsafe fn mmap_raw(fd: i32, length: size_t) -> FrozenRes<TPtr> {
    let ptr = mmap(
        ptr::null_mut(),
        length,
        PROT_WRITE | PROT_READ,
        MAP_SHARED,
        fd,
        0 as off_t,
    );

    if ptr == MAP_FAILED {
        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // invalid fd, invalid fd type, invalid length, etc.
            EINVAL | EBADF | EACCES | EOVERFLOW => return new_err(FMMapErrRes::Hcf, err_msg),

            // no more memory available
            ENOMEM => return new_err(FMMapErrRes::Nmm, err_msg),

            _ => return new_err(FMMapErrRes::Unk, err_msg),
        };
    }

    Ok(ptr)
}

unsafe fn munmap_raw(ptr: TPtr, length: size_t) -> FrozenRes<()> {
    if munmap(ptr, length) == 0 {
        return Ok(());
    }

    let errno = last_errno();
    let err_msg = err_msg(errno);

    match errno {
        // invalid/unaligned ptr or address range is not mapped
        EINVAL | ENOMEM => new_err(FMMapErrRes::Hcf, err_msg),

        _ => new_err(FMMapErrRes::Unk, err_msg),
    }
}

unsafe fn msync_raw(ptr: TPtr, length: size_t) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        let res = msync(ptr, length, MS_SYNC);
        if hints::likely(res == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt, locked file or fatel error
            EINTR | EBUSY => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FMMapErrRes::Syn, err_msg);
            }

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(FMMapErrRes::Syn, err_msg),

            // invalid fd or lack of support for sync
            EINVAL => return new_err(FMMapErrRes::Hcf, err_msg),

            // no-more memory available
            ENOMEM => return new_err(FMMapErrRes::Nmm, err_msg),

            _ => return new_err(FMMapErrRes::Unk, err_msg),
        }
    }
}

#[inline]
fn last_errno() -> i32 {
    #[cfg(target_os = "linux")]
    unsafe {
        *libc::__errno_location()
    }

    #[cfg(target_os = "macos")]
    unsafe {
        *libc::__error()
    }
}

#[inline]
unsafe fn err_msg(errno: i32) -> Vec<u8> {
    let ptr = strerror(errno);
    if ptr.is_null() {
        return Vec::new();
    }

    CStr::from_ptr(ptr).to_bytes().to_vec()
}
