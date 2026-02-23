use super::{new_err, new_err_default, FFId, FFileErrRes};
use crate::{error::FrozenRes, hints};
use libc::{
    access, c_char, c_int, c_uint, c_void, close, fstat, ftruncate, iovec, off_t, open, pread, preadv, pwrite, pwritev,
    size_t, stat, sysconf, unlink, EACCES, EBADF, EFAULT, EINTR, EINVAL, EIO, EISDIR, EMSGSIZE, ENOENT, ENOSPC,
    ENOTDIR, EOPNOTSUPP, EPERM, EROFS, ESPIPE, F_OK, O_CLOEXEC, O_CREAT, O_DIRECTORY, O_RDONLY, O_RDWR, S_IRUSR,
    S_IWUSR, _SC_IOV_MAX,
};
use std::{
    ffi::CStr,
    sync::{atomic, OnceLock},
};

const CLOSED_FD: FFId = FFId::MIN;
static IOV_MAX_CACHE: OnceLock<usize> = OnceLock::new();

/// max allowed retries for `EINTR` errors
const MAX_RETRIES: usize = 0x0A / 2;

/// max iovecs allowed for single readv/writev calls
const MAX_IOVECS: usize = 0x200;

/// Custom impl of `std::fs::File` for posix systems
#[derive(Debug)]
pub(super) struct POSIXFile(atomic::AtomicI32);

unsafe impl Send for POSIXFile {}
unsafe impl Sync for POSIXFile {}

impl POSIXFile {
    /// Read file descriptor of [`POSIXFile`]
    #[inline]
    pub(super) fn fd(&self) -> FFId {
        self.0.load(atomic::Ordering::Acquire)
    }

    /// check if [`POSIXFile`] exists on storage device or not
    ///
    /// ## How it works
    ///
    /// By using `access(2)` syscall w/ `F_OK`, we check whether the calling process
    /// can resolve the given `path` in underlying fs
    pub(super) unsafe fn exists(path: &std::path::PathBuf) -> FrozenRes<bool> {
        let cpath = path_to_cstring(path)?;
        Ok(access(cpath.as_ptr(), F_OK) == 0)
    }

    /// create a new or open an existing [`POSIXFile`]
    ///
    /// ## Crash safe durability
    ///
    /// In POSIX systems, `open(O_CREATE)` only creates the directory entry in memory, it may be
    /// visible immediately, but the file entry is not crash durable on many fs
    ///
    /// On some linux systems, journaling fs (ext4, xfs, etc) often replay their journal on mount
    /// after a crash is observed, which usually restores recent directory updates, i.e. our newly created
    /// file entry, as a result newly created file often survive the crash
    ///
    /// In our case, when a new [`FrozenFile`] is created, we zero-extend it using `ftruncate()`,
    /// and perform `fdatasync()` or `fcntl(F_FULLSYNC)`, which in result provides us the crash safe
    /// durability we need
    pub(super) unsafe fn new(path: &std::path::PathBuf) -> FrozenRes<Self> {
        let fd = open_raw(path, prep_flags())?;
        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// Close [`POSIXFile`] to give up allocated resources
    ///
    /// This function is idempotent, hence it prevents close-on-close errors
    ///
    /// ## Sync Error (`FFileErrRes::Syn`)
    ///
    /// In POSIX systems, kernel may report delayed write/sync failures when closing, this are
    /// durability errors, fatal for us
    ///
    /// we can easily tackle this error for each bach of writes by enforcing hard durability
    /// guaranties right after the write ops, and making sure they are completed without errors
    ///
    /// this provides strong durability for the storage engine, and if `EIO` occurs, anyhow,
    /// we treat it as `FFileErrRes::Hcf` i.e. impl failure
    pub(super) unsafe fn close(&self) -> FrozenRes<()> {
        let fd = self.0.swap(CLOSED_FD, atomic::Ordering::AcqRel);
        if fd == CLOSED_FD {
            return Ok(());
        }

        close_raw(fd)
    }

    /// Deletes the [`POSIXFile`] entery from the fs
    pub(super) unsafe fn unlink(&self, path: &std::path::PathBuf) -> FrozenRes<()> {
        let cpath = path_to_cstring(path)?;

        // NOTE: POSIX systems requires fd to be closed before attempting to unlink the file
        self.close()?;

        if unlink(cpath.as_ptr()) == 0 {
            // NOTE: In POSIX systems, `unlink(path)` only updates the entry in memory, and
            // does not guaranty crash safe durability for the operation, we must perform
            // `fsync` on the directory to make sure we get crash safe durability
            return sync_parent_dir(path);
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // missing file or invalid path
            ENOENT | ENOTDIR => return new_err(FFileErrRes::Inv, err_msg),

            // lack of permission or read only fs
            EACCES | EPERM | EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // NOTE: In POSIX systems, kernel may report delayed io failures on `unlink`,
            // this are fatal errors, and can not be retried
            //
            // We protect this by enforcing hard durability right after write ops, so the
            // occurrence of this error is an implementation failure
            EIO => return new_err(FFileErrRes::Hcf, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }

    /// Read current length of [`POSIXFile`] using file metadata (w/ `fstat` syscall)
    pub(super) unsafe fn length(&self) -> FrozenRes<usize> {
        let mut st = core::mem::zeroed::<stat>();
        let res = fstat(self.fd(), &mut st);

        if res != 0 {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // bad or invalid fd
            if errno == EBADF || errno == EFAULT {
                return new_err(FFileErrRes::Hcf, err_msg);
            }

            return new_err(FFileErrRes::Unk, err_msg);
        }

        Ok(st.st_size as usize)
    }

    /// Grow (zero extend) [`POSIXFile`] w/ given `len_to_add`
    pub(super) unsafe fn grow(&self, curr_len: usize, len_to_add: usize) -> FrozenRes<usize> {
        let fd = self.fd();

        // NOTE: Not all kernel versions, fs (such as networked fs), support this syscall,
        // in such cases we must fallback to using `ftruncate`
        #[cfg(target_os = "linux")]
        if fallocate_raw(fd, curr_len, len_to_add)? == false {
            ftruncate_raw(fd, curr_len, len_to_add)?;
        }

        #[cfg(target_os = "macos")]
        {
            ftruncate_raw(fd, curr_len, len_to_add)?;

            // INFO: we have option to hint the kernel to preallocate the range, to decrease the
            // latency for future write ops on the newly added range
            f_preallocate_raw(fd, curr_len, len_to_add)?;
        }

        self.length()
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
    /// is guaranteed, so the syscall must be retried
    ///
    /// ## `F_FULLFSYNC` vs `fsync`
    ///
    /// The supposed best os, i.e. mac, does not provide strong durability via `fsync()`, hence writes/updates
    /// may lost on crash or power failure, as it does not provide strong durability (instant flush), read docs for
    /// more info [https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/fsync.2.html]
    ///
    /// To achieve true crash durability (including protection against power loss, sudden crash), we have to use
    /// the `fcntl(fd, F_FULLFSYNC)` syscall
    ///
    /// ## Fallback to `fsync`
    ///
    /// `fcntl(F_FULLSYNC)` may result in `EINVAL` or `ENOTSUP` on fs which may not support it, such as network fs,
    /// FUSE mounts, FAT32 volumes, or some external devices
    ///
    /// To guard this, we fallback to `fsync()`, which does not guaranty durability for sudden crash or
    /// power loss, which is acceptable when strong durability is simply not available or allowed
    #[cfg(target_os = "macos")]
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        f_fullsync_raw(self.fd())
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
    /// is guaranteed, so the syscall must be retried
    ///
    /// ## `fsync` vs `fdatasync`
    ///
    /// We use `fdatasync()` instead of `fsync()` for persistence, as it guarantees, all updates/writes and
    /// any metadata, such as file size, are flushed to stable storage
    ///
    /// With combonation of `O_NOATIME` and `fdatasync()`, we avoid non-essential metadata updates, such as
    /// access time (`atime`), modification time (`mtime`), and other bookkeeping info
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        fdatasync_raw(self.fd())
    }

    /// Initiates writeback (best-effort) of dirty pages in the specified range
    ///
    /// ## Why
    ///
    /// In our case, `sync_range` is used as a prompt for the kernel to start flushing dirty pages in the
    /// specified range, which result in reduced latency for `fdatasync` and `fcntl(F_FULLSYNC)` syscalls
    ///
    /// This syscall, by itself, does not guarantee any kind of durability, and must always be paired with
    /// strong sync calls like `fdatasync()` and `fcntl(F_FULLSYNC)`
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync_range(&self, offset: usize, len: usize) -> FrozenRes<()> {
        sync_file_range_raw(self.fd(), offset, len)
    }

    /// Read a single `iovec` from given `offset` w/ `pread` syscall
    #[inline(always)]
    pub(super) unsafe fn pread(&self, iov: &mut iovec, offset: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let mut read = 0usize;

        while read < iov.iov_len {
            let res = pread(
                fd,
                (iov.iov_base as *mut u8).add(read) as *mut c_void,
                (iov.iov_len - read) as size_t,
                (offset + read) as off_t,
            );

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(FFileErrRes::Hcf);
            }

            if hints::unlikely(res < 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // io interrupt
                    EINTR => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(FFileErrRes::Prm, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            read += res as usize;
        }

        Ok(())
    }

    /// Write a single `iovec` at given `offset` w/ `pwrite` syscall
    #[inline(always)]
    pub(super) unsafe fn pwrite(&self, iov: &iovec, offset: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let mut written = 0usize;

        while written < iov.iov_len {
            let res = pwrite(
                fd,
                (iov.iov_base as *mut u8).add(written) as *mut c_void,
                (iov.iov_len - written) as size_t,
                (offset + written) as off_t,
            );

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(FFileErrRes::Hcf);
            }

            if hints::unlikely(res <= 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // io interrupt
                    EINTR => continue,

                    // permission denied or read-only fs
                    EACCES | EPERM | EROFS => return new_err(FFileErrRes::Prm, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            written += res as usize;
        }

        Ok(())
    }

    /// Read multiple `iovec` objects starting from given `offset` w/ `preadv` syscall
    ///
    /// ## NOTES
    ///
    /// - All `iovec` objects in given `[iovec]` slice must be of same length
    /// - The caller must not try to read byound current length of `[POSIXFile]`
    #[inline(always)]
    pub(super) unsafe fn preadv(&self, iovecs: &mut [iovec], offset: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let max_iovs = read_max_iovecs();

        let iovecs_len = iovecs.len();
        let iov_size = iovecs[0].iov_len;

        let mut head = 0usize;
        let mut off = offset as off_t;

        while head < iovecs_len {
            let remaining_iov = iovecs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iovecs.as_ptr().add(head);

            let res = preadv(fd, ptr, cnt, off);

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(FFileErrRes::Hcf);
            }

            if res < 0 {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    EINTR => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(FFileErrRes::Prm, err_msg),

                    // invalid fd, bad pointer, illegal seek, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE | EMSGSIZE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            // NOTE:
            //
            // In POSIX systems, preadv syscall may,
            // - read fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // even though this behavior is situation and fs dependent (well, according to my short research),
            // we opt to handle it for correctness across different systems

            off += res as off_t;

            let written = res as usize;
            let full_pages = written / iov_size;
            let partial = written % iov_size;

            // fully written pages
            head += full_pages;

            // partially written page (rare)
            if partial > 0 {
                let iov = &mut iovecs[head];
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
            }
        }

        Ok(())
    }

    /// Write multiple `iovec` objects starting from given `offset` w/ `writev` syscall
    ///
    /// ## NOTES
    ///
    /// - All `iovec` objects in given `[iovec]` slice must be of same length
    /// - The caller must not try to write byound current length of `[POSIXFile]`
    #[inline(always)]
    pub(super) unsafe fn pwritev(&self, iovecs: &mut [iovec], offset: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let max_iovs = read_max_iovecs();

        let iovecs_len = iovecs.len();
        let iov_size = iovecs[0].iov_len;

        let mut head = 0usize;
        let mut off = offset as off_t;

        while head < iovecs_len {
            let remaining_iov = iovecs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iovecs.as_ptr().add(head);

            let res = pwritev(fd, ptr, cnt, off);

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(FFileErrRes::Hcf);
            }

            if res < 0 {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    EINTR => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(FFileErrRes::Prm, err_msg),

                    // invalid fd, bad pointer, illegal seek, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE | EMSGSIZE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            // NOTE:
            //
            // In POSIX systems, pwritev syscall may,
            // - write fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // even though this behavior is situation and fs dependent (well, according to my short research),
            // we opt to handle it for correctness across different systems

            off += res as off_t;

            let written = res as usize;
            let full_pages = written / iov_size;
            let partial = written % iov_size;

            // fully written pages
            head += full_pages;

            // partially written page (rare)
            if partial > 0 {
                let iov = &mut iovecs[head];
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
            }
        }

        Ok(())
    }
}

/// create/open a new file w/ `open` syscall
///
/// ## Caveats of `O_NOATIME` (`EPERM` err_msg)
///
/// `open()` with `O_NOATIME` may fail with `EPERM` instead of silently ignoring the flag
///
/// `EPERM` indicates a kernel level permission violation, as the kernel rejects the
/// request outright, even though the flag only affects metadata behavior
///
/// To remain sane across ownership models, containers, and shared filesystems,
/// we explicitly retry the `open()` w/o `O_NOATIME` when `EPERM` is encountered
unsafe fn open_raw(path: &std::path::PathBuf, flags: c_int) -> FrozenRes<FFId> {
    let cpath = path_to_cstring(path)?;

    // write + read permissions
    let perm = (S_IRUSR | S_IWUSR) as c_uint;

    #[cfg(target_os = "linux")]
    let (mut flags, mut tried_noatime) = (flags, false);

    loop {
        let fd = if flags & O_CREAT != 0 {
            open(cpath.as_ptr(), flags, perm)
        } else {
            open(cpath.as_ptr(), flags)
        };

        if hints::unlikely(fd < 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // NOTE: if the error is EPERM and flags contains O_NOATIME flag, we try to open again
            // w/o the O_NOATIME flag, as some fs does not support this flag

            #[cfg(target_os = "linux")]
            if errno == EPERM && (flags & libc::O_NOATIME) != 0 && !tried_noatime {
                flags &= !libc::O_NOATIME;
                tried_noatime = true;
                continue;
            }

            match errno {
                // NOTE: We must retry on interuption errors (EINTR retry)
                EINTR => continue,

                // no space available on disk
                ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

                // path is a dir (hcf)
                EISDIR => return new_err(FFileErrRes::Hcf, err_msg),

                // invalid path (missing sub dir's)
                ENOENT | ENOTDIR => return new_err(FFileErrRes::Inv, err_msg),

                // permission denied or read-only fs
                EACCES | EPERM | EROFS => return new_err(FFileErrRes::Prm, err_msg),

                _ => return new_err(FFileErrRes::Unk, err_msg),
            }
        }

        return Ok(fd);
    }
}

unsafe fn close_raw(fd: FFId) -> FrozenRes<()> {
    if close(fd) == 0 {
        return Ok(());
    }

    let errno = last_errno();
    let err_msg = err_msg(errno);

    // POSIX allowes `close(fd)` to return `EINTR` when the fd is already closed
    if errno == EINTR {
        return Ok(());
    }

    // NOTE: In POSIX systems, kernel may report delayed io failures on `close`,
    // this are fatal errors, and can not be retried
    //
    // We protect this by enforcing hard durability right after write ops, so the
    // occurrence of this error is an implementation failure
    if errno == EIO {
        return new_err(FFileErrRes::Hcf, err_msg);
    }

    return new_err(FFileErrRes::Unk, err_msg);
}

#[cfg(target_os = "linux")]
unsafe fn fdatasync_raw(fd: FFId) -> FrozenRes<()> {
    let mut retries = 0; // only for EIO & EINTR errors
    loop {
        if hints::likely(libc::fdatasync(fd) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt (must retry)
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FFileErrRes::Syn, err_msg);
            }

            // invalid fd or lack of support for sync
            EINVAL | EBADF => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            //
            // NOTE: this must be handled seperately, cuase, if this error occurs,
            // the storage system must act, mark recent writes as failed or notify users,
            // etc. to keep the system robust and fault tolerent!
            EIO => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FFileErrRes::Syn, err_msg);
            }

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }
}

#[cfg(target_os = "macos")]
unsafe fn f_fullsync_raw(fd: FFId) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::likely(libc::fcntl(fd, libc::F_FULLFSYNC) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FFileErrRes::Syn, err_msg);
            }

            // lack of support for `F_FULLSYNC`
            libc::ENOTSUP | EOPNOTSUPP => break,

            // invalid fd or bad impl
            EINVAL | EBADF => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(FFileErrRes::Syn, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }

    // NOTE: when the storage device or fs, does not support fullsync, we fallback to `fsync()`,
    // which does not guaranty durability for sudden crash or power loss, which is acceptable when
    // strong durability is simply not available or allowed
    fsync_raw(fd)
}

/// Syncs in cache data updates on the storage device
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
/// is guaranteed, so the syscall must be retried
unsafe fn fsync_raw(fd: FFId) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::unlikely(libc::fsync(fd) != 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            match errno {
                // IO interrupt
                EINTR => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(FFileErrRes::Syn, err_msg);
                }

                // invalid fd or lack of support for sync
                EBADF | EINVAL => return new_err(FFileErrRes::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(FFileErrRes::Prm, err_msg),

                // fatal error, i.e. no sync for writes in recent window/batch
                EIO => return new_err(FFileErrRes::Syn, err_msg),

                _ => return new_err(FFileErrRes::Unk, err_msg),
            }
        }

        return Ok(());
    }
}

#[cfg(target_os = "linux")]
unsafe fn sync_file_range_raw(fd: FFId, offset: usize, len: usize) -> FrozenRes<()> {
    let flag = libc::SYNC_FILE_RANGE_WRITE;
    let mut retries = 0; // only for EINTR errors

    loop {
        let res = libc::sync_file_range(fd, offset as off_t, len as off_t, flag);
        if hints::likely(res == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FFileErrRes::Syn, err_msg);
            }

            // invalid fd or lack of support for sync
            EBADF | EINVAL => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(FFileErrRes::Syn, err_msg),

            // NOTE: on many fs mainly ones w/o local journaling, and older kernels does not support
            // `sync_file_range(SYNC_FILE_RANGE_WRITE)`, also as the use of this is only to hint the
            // fs (for perf gains for later sync), we simply let go of this and do not elivate any
            // kind of errors
            EOPNOTSUPP | libc::ENOSYS => return Ok(()),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }
}

/// extend the [`POSIXFile`] to `len = curr_len + len_to_add`, reserves disk block for newly added
/// range, and guarantees reads return zero after file size is extended
///
/// Returns,
///
/// - `Ok(true)` if operation is supported and was successful
/// - `Ok(false)` when operation is simply not supported, must fallback to `ftruncate()`
///
/// ## Support on fs
///
/// Not all kernel versions, fs (such as networked fs), support this syscall, in such cases we must
/// fallback to using `ftruncate`
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
/// is guaranteed, so the syscall must be retried
#[cfg(target_os = "linux")]
unsafe fn fallocate_raw(fd: FFId, curr_len: usize, len_to_add: usize) -> FrozenRes<bool> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::likely(libc::fallocate(fd, 0, curr_len as off_t, len_to_add as off_t) == 0) {
            return Ok(true);
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(FFileErrRes::Grw, err_msg);
            }

            // invalid fd
            EBADF | EINVAL => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // no space available on disk to grow
            ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

            // NOTE: on many fs `fallocate` may not be supported due to old kernel or fs
            // limitations, as use of this is only to hint the fs (for perf gains while writes),
            // we simply let go of this and do not elivate any kind of errors
            EOPNOTSUPP | libc::ENOSYS => return Ok(false),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }
}

/// sets the size of [`POSIXFile`] to `len = curr_len + len_to_add` on fs
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
/// is guaranteed, so the syscall must be retried
unsafe fn ftruncate_raw(fd: FFId, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
    let new_len = (curr_len + len_to_add) as off_t;
    let mut retries = 0; // only for EINTR errors

    loop {
        if hints::likely(ftruncate(fd, new_len) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(FFileErrRes::Grw, err_msg);
            }

            // invalid fd or lack of support for sync
            EINVAL | EBADF => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            // no space available on disk to grow
            ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }
}

/// disk space (best-effort) preallocations using `F_PREALLOCATE`
///
/// ## Semantics
///
/// This syscall does not change the size, nor the file capacity, the use is to attempt to reserve
/// disk blocks in advance to letency during write ops to the [`POSIXFile`]
///
/// ## Contiguous vs Non-contiguous Allocations
///
/// In `F_PREALLOCATE` calls, we get two allocation modes, contiguous and non-contiguous,
///
/// Calls w/ `F_ALLOCATECONTIG` are more likely to fail on fragmented fs, so we instantly fallback
/// to using `F_ALLOCATEALL` for reliability and correctness
///
/// ## Caveats (more like stupidity) of `F_ALLOCATEALL`
///
/// The preallocations may be revoked by fs due to (intentional) waker semantics, this acts more like a hint
/// and not a command to the fs, so the perf is not always guaranteed
#[cfg(target_os = "macos")]
unsafe fn f_preallocate_raw(fd: FFId, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors

    // NOTE: by default we try w/ contiguous allocations for optimal perf, when not available,
    // i.e. received `ENOSPC`, we fallback to non-contiguous allocations
    let mut store = libc::fstore_t {
        fst_flags: libc::F_ALLOCATECONTIG,
        fst_posmode: libc::F_PEOFPOSMODE,
        fst_offset: curr_len as off_t,
        fst_length: len_to_add as off_t,
        fst_bytesalloc: 0,
    };

    loop {
        if libc::fcntl(fd, libc::F_PREALLOCATE, &store) == 0 {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(FFileErrRes::Grw, err_msg);
            }

            // no space available on disk to grow
            ENOSPC => {
                // NOTE: we must retry w/ non-contiguous allocs for correctness, as sometimes
                // we do get `ENOSPC` only for contiguous allocs
                if store.fst_flags == libc::F_ALLOCATECONTIG {
                    store.fst_flags = libc::F_ALLOCATEALL;
                    retries = 0;
                    continue;
                }

                return new_err(FFileErrRes::Nsp, err_msg);
            }

            // NOTE: on many fs `fcntl(F_PREALLOCATE)` may not be supported due to old kernel
            // or fs limitations, as use of this is only to hint the fs (for perf gains while writes),
            // we simply let go of this and do not elivate any kind of errors
            EOPNOTSUPP | libc::ENOTSUP => return Ok(()),

            // invalid fd or lack of support
            EBADF | EINVAL => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only file system
            EROFS => return new_err(FFileErrRes::Prm, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
        }
    }
}

/// perform `fsync` for parent directory of file at given `path`
///
/// ## Purpose
///
/// In POSIX systems, syscalls like `open(path)`, `close(fd)` and `unlink(path)`, does not provide
/// crash safe durability, hence after a sudden crash or power loss, the operation may reverse,
/// resulting in catastrophic consequences
///
/// we must `fsync(parent_dir)`, for crash safe durability
unsafe fn sync_parent_dir(path: &std::path::PathBuf) -> FrozenRes<()> {
    let parent = extract_parent_dir(path);
    let flags = O_RDONLY | O_DIRECTORY | O_CLOEXEC;
    let fd = open_raw(&parent, flags)?;

    #[cfg(target_os = "linux")]
    let res = fsync_raw(fd);

    #[cfg(target_os = "macos")]
    let res = f_fullsync_raw(fd);

    let _ = close_raw(fd);

    res
}

/// preps flags for `open()` syscall
///
/// ## Access Time Updates (O_NOATIME)
///
/// On linux, we can use the `O_NOATIME` flag to disable access time updates on the [`POSIXFile`]
///
/// Normally every I/O operation triggers an `atime` update for every write to disk, w/ use of
/// this flag, we try to eliminate counterproductive measures
///
/// ## Limitations of `O_NOATIME`
///
/// - not all fs support this flag, many silently ignore it, but some throw `EPERM` error
/// - It only works when the UID's are matched for calling processe and file owner
#[cfg(target_os = "linux")]
fn prep_flags() -> c_int {
    return O_RDWR | O_CLOEXEC | libc::O_NOATIME | O_CREAT;
}

/// preps flags for `open()` syscall
#[cfg(target_os = "macos")]
fn prep_flags() -> c_int {
    return O_RDWR | O_CLOEXEC | O_CREAT;
}

/// convert a `std::path::PathBuf` into `std::ffu::CString`
fn path_to_cstring(path: &std::path::PathBuf) -> FrozenRes<std::ffi::CString> {
    match std::ffi::CString::new(path.as_os_str().as_encoded_bytes()) {
        Ok(cs) => Ok(cs),
        Err(e) => new_err(FFileErrRes::Inv, e.into_vec()),
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

/// fetch max allowed `iovecs` per `preadv` & `pwritev` syscalls
fn read_max_iovecs() -> usize {
    *IOV_MAX_CACHE.get_or_init(|| unsafe {
        let res = sysconf(_SC_IOV_MAX);
        if res <= 0 {
            MAX_IOVECS
        } else {
            res as usize
        }
    })
}

fn extract_parent_dir(path: &std::path::PathBuf) -> std::path::PathBuf {
    match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => std::path::Path::new(".").to_path_buf(),
    }
}
