use fe::FRes;
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINVAL, EIO, ENOMEM, EOVERFLOW, MAP_FAILED,
    MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};
use std::sync::atomic;

use crate::{error::new_error, FMErr};

pub(crate) struct MMap(*mut c_void);

unsafe impl Send for MMap {}
unsafe impl Sync for MMap {}

impl MMap {
    pub(super) unsafe fn new(fd: i32, len: size_t, mid: u8) -> FRes<Self> {
        let ptr = mmap(
            std::ptr::null_mut(),
            len,
            PROT_WRITE | PROT_READ,
            MAP_SHARED,
            fd,
            0 as off_t,
        );

        if ptr == MAP_FAILED {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid fd, invalid fd type, invalid length, etc.
            if err_raw == Some(EINVAL)
                || err_raw == Some(EBADF)
                || err_raw == Some(EACCES)
                || err_raw == Some(EOVERFLOW)
            {
                return new_error(mid, FMErr::Hcf, error);
            }

            // no more memory space available
            if err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Nsp, error);
            }

            // unknown (unsupported, etc.)
            return new_error(mid, FMErr::Unk, error);
        }

        return Ok(Self(ptr));
    }

    pub(crate) unsafe fn unmap(&self, length: usize, mid: u8) -> FRes<()> {
        if munmap(self.0, length) != 0 {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid or unaligned pointer
            if err_raw == Some(EINVAL) || err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Hcf, error);
            }

            // unknown
            return new_error(mid, FMErr::Unk, error);
        }

        Ok(())
    }

    pub(super) unsafe fn sync(&self, length: usize, mid: u8) -> FRes<()> {
        // only for EIO and EBUSY errors
        const MAX_RETRIES: usize = 4;
        let mut retries = 0;

        loop {
            if msync(self.0, length, MS_SYNC) != 0 {
                let error = last_os_error();
                let error_raw = error.raw_os_error();

                // IO interrupt (must retry)
                if error.kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }

                // invalid fd or lack of support for sync
                if error_raw == Some(ENOMEM) || error_raw == Some(EINVAL) {
                    return new_error(mid, FMErr::Hcf, error);
                }

                // locked file or fatel error, i.e. unable to sync
                //
                // NOTE: this is handled seperately, as if this error occurs, we must
                // notify users that the sync failed, hence the data is not persisted
                if error_raw == Some(EIO) || error_raw == Some(EBUSY) {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        std::thread::yield_now();
                        continue;
                    }

                    // retries exhausted and durability is broken in the current window
                    return new_error(mid, FMErr::Syn, error);
                }

                return new_error(mid, FMErr::Unk, error);
            }

            return Ok(());
        }
    }

    #[inline]
    pub(crate) const unsafe fn get<T>(&self, offset: usize) -> *const T {
        // sanity check
        debug_assert!(offset % 8 == 0, "Offset must be 8 bytes aligned");
        self.0.add(offset) as *const T
    }

    #[inline]
    pub(crate) const unsafe fn get_mut<T>(&self, offset: usize) -> *mut T {
        // sanity check
        debug_assert!(offset % 0x8 == 0, "Offset must be 8 bytes aligned");
        self.0.add(offset) as *mut T
    }
}

#[inline]
fn last_os_error() -> std::io::Error {
    std::io::Error::last_os_error()
}
