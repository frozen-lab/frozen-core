use super::{new_err, FMMapErrRes};
use crate::{error::FrozenRes, hints};
use core::{ffi::CStr, ptr, sync::atomic};
use libc::{
    c_char, c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, EOVERFLOW,
    MAP_FAILED, MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

type TPtr = *mut c_void;

/// max allowed retries for `EINTR` errors
const MAX_RETRIES: usize = 0x0A / 2;

/// Raw implementation of Posix (linux & macos) `memmap` for [`FrozenMMap`]
#[derive(Debug)]
pub(super) struct POSIXMMap {
    ptr: TPtr,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] w/ given `fd` and `length`
    pub(super) unsafe fn new(fd: i32, length: size_t) -> FrozenRes<Self> {
        let ptr = mmap_raw(fd, length)?;
        return Ok(Self {
            ptr,
            unmapped: atomic::AtomicBool::new(false),
        });
    }

    /// Close [`POSIXMMap`] to give up allocated resources
    ///
    /// This function is idempotent, hence it prevents unmap-on-unmap errors
    pub(super) unsafe fn unmap(&self, length: usize) -> FrozenRes<()> {
        if self
            .unmapped
            .compare_exchange(false, true, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            .is_err()
        {
            return Ok(());
        }

        mumap_raw(self.ptr, length)
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
        msync_raw(self.ptr, length)
    }

    /// Get an immutable typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get<T>(&self, offset: usize) -> *const T {
        self.ptr.add(offset) as *const T
    }

    /// Get a mutable (read/write) typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get_mut<T>(&self, offset: usize) -> *mut T {
        self.ptr.add(offset) as *mut T
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

unsafe fn mumap_raw(ptr: TPtr, length: size_t) -> FrozenRes<()> {
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
            EINTR | EBUSY | EIO => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FMMapErrRes::Syn, err_msg);
            }

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
    const BUF_LEN: usize = 0x100;
    let mut buf = [c_char::default(); BUF_LEN];

    if libc::strerror_r(errno, buf.as_mut_ptr(), BUF_LEN) != 0 {
        return Vec::new();
    }

    let cstr = CStr::from_ptr(buf.as_ptr());
    return cstr.to_bytes().to_vec();
}
