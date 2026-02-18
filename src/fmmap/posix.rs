use super::{new_err, FMMapErrRes};
use crate::{error::FrozenRes, hints};
use alloc::vec::Vec;
use core::{ffi::CStr, ptr, sync::atomic};
use libc::{
    c_char, c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, MAP_FAILED,
    MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors

/// Raw implementation of Posix (linux & macos) `memmap` for [`FrozenMMap`]
pub(super) struct POSIXMMap {
    ptr: *mut c_void,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] instance for given `fd` w/ read & write permissions
    pub(super) unsafe fn new(fd: i32, length: size_t) -> FrozenRes<Self> {
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

            // invalid fd, invalid fd type, invalid length, etc.
            if errno == EINVAL || errno == EBADF || errno == EACCES {
                return new_err(FMMapErrRes::Hcf, err_msg);
            }

            // no more memory space available
            if errno == ENOMEM {
                return new_err(FMMapErrRes::Nmm, err_msg);
            }

            // unknown (unsupported, etc.)
            return new_err(FMMapErrRes::Unk, err_msg);
        }

        return Ok(Self {
            ptr,
            unmapped: atomic::AtomicBool::new(false),
        });
    }

    /// Unmap (free/drop) the mmaped instance of [`POSIXMMap`]
    pub(super) unsafe fn unmap(&self, length: usize, mid: u8) -> FrozenRes<()> {
        // NOTE: To avoid another thread/process from executing munmap, we mark unmapped before even
        // trying to unmap, this kind of wroks like mutex, as we reassign to false on failure
        if self
            .unmapped
            .compare_exchange(false, true, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            .is_err()
        {
            return Ok(());
        }

        if munmap(self.ptr, length) != 0 {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // invalid or unaligned pointer
            if errno == EINVAL || errno == ENOMEM {
                return new_err(FMMapErrRes::Hcf, err_msg);
            }

            // unknown (fallback)
            return new_err(FMMapErrRes::Unk, err_msg);
        }

        Ok(())
    }

    /// Syncs in-mem data on the storage device
    pub(super) unsafe fn sync(&self, length: usize, mid: u8) -> FrozenRes<()> {
        // only for EIO and EBUSY errors
        let mut retries = 0;

        loop {
            let res = msync(self.ptr, length, MS_SYNC);
            if hints::unlikely(res != 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                // IO interrupt (must retry)
                if errno == EINTR {
                    continue;
                }

                // invalid fd or lack of support for sync
                if errno == ENOMEM || errno == EINVAL {
                    return new_err(FMMapErrRes::Hcf, err_msg);
                }

                // locked file or fatel error, i.e. unable to sync
                //
                // NOTE: this is handled seperately, as if this error occurs, we must
                // notify users that the sync failed, hence the data is not persisted
                if errno == EIO || errno == EBUSY {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // retries exhausted and durability is broken in the current window
                    return new_err(FMMapErrRes::Syn, err_msg);
                }

                return new_err(FMMapErrRes::Unk, err_msg);
            }

            return Ok(());
        }
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
