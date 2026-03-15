//! Utilities for error propagation used across `[frozen_core]`
//!
//! This module provides,
//!
//! - [`FrozenErr`]: a structured error w/ 32-bit identifier
//! - [`FrozenRes`]: a result alias using [`FrozenErr`]
//!
//! ## Id
//!
//! Each [`FrozenErr`] uses a 32-bit identifier encoded in following format,
//!
//! `| module:8 | domain:8 | reason:16 |`
//!
//! This id packs important context which aids in the debugging process
//!
//! ## Example
//!
//! ```
//! use frozen_core::error::{FrozenErr, FrozenRes};
//!
//! fn read_file() -> FrozenRes<()> {
//!     Err(FrozenErr::new(1, 2, 0x0033, b"io", b"read failed"))
//! }
//!
//! let err = read_file().unwrap_err();
//!
//! assert_eq!(err.id, 0x0102_0033);
//! assert!(err.context.contains("[io]"));
//! ```

/// Custom result type w/ [`FrozenErr`] as error type
pub type FrozenRes<T> = Result<T, FrozenErr>;

/// Utilities for error propagation used across `[frozen_core]`
#[derive(Debug, Clone)]
pub struct FrozenErr {
    /// Encoded 32-bit unique identifier for [`FrozenErr`]
    pub id: u32,

    /// Error context for the [`FrozenErr`]
    pub context: String,
}

impl FrozenErr {
    /// Construct a new [`FrozenErr`]
    ///
    /// ## Example
    ///
    /// ```
    /// let err = frozen_core::error::FrozenErr::new(1, 2, 0x0033, b"io", b"failed to read file");
    ///
    /// assert_eq!(err.id, 0x0102_0033);
    /// assert!(err.context.contains("[io]"));
    /// assert!(err.context.contains("failed to read file"));
    /// ```
    #[inline(always)]
    pub fn new(module: u8, domain: u8, reason: u16, detail: &'static [u8], errmsg: &[u8]) -> Self {
        let detail_str = String::from_utf8_lossy(detail).to_string();
        let errmsg_str = String::from_utf8_lossy(errmsg).to_string();

        Self {
            id: error_id(module, domain, reason),
            context: format!("[{}] {}", detail_str, errmsg_str),
        }
    }

    /// Construct a new [`FrozenErr`] from raw [`Error`] object
    ///
    /// ## Example
    ///
    /// ```
    /// let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "file missing");
    /// let err = frozen_core::error::FrozenErr::new_raw(1, 2, 0x0033, b"io", io_err);
    ///
    /// assert_eq!(err.id, 0x0102_0033);
    /// assert!(err.context.contains("[io]"));
    /// assert!(err.context.contains("file missing"));
    /// ```
    #[inline(always)]
    pub fn new_raw<E: std::fmt::Display>(module: u8, domain: u8, reason: u16, detail: &'static [u8], err: E) -> Self {
        let detail_str = String::from_utf8_lossy(detail).to_string();
        let errmsg_str = err.to_string();

        Self {
            id: error_id(module, domain, reason),
            context: format!("[{}] {}", detail_str, errmsg_str),
        }
    }

    /// Compare two errors by their encoded id's
    ///
    /// ## Example
    ///
    /// ```
    /// let err1 = frozen_core::error::FrozenErr::new(0, 0, 0x30, b"test", b"something failed");
    /// let err2 = frozen_core::error::FrozenErr::new(0, 0, 0x30, b"test", b"another message");
    ///
    /// assert!(err1.compare_id(&err2));
    /// ```
    #[inline(always)]
    pub fn compare_id(&self, err: &FrozenErr) -> bool {
        self.id == err.id
    }
}

#[inline(always)]
const fn error_id(module: u8, domain: u8, reason: u16) -> u32 {
    ((module as u32) << 0x18) | ((domain as u32) << 0x10) | (reason as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[inline]
    const fn from_error_id(eid: u32) -> (u8, u8, u16) {
        let module = ((eid >> 24) & 0xff) as u8;
        let domain = ((eid >> 16) & 0xff) as u8;
        let reason = (eid & 0xffff) as u16;

        (module, domain, reason)
    }

    #[test]
    fn ok_context_exact_format() {
        let err = FrozenErr::new(1, 2, 3, b"io", b"failure");
        assert_eq!(err.context, "[io] failure");
    }

    #[test]
    fn ok_empty_message() {
        let err = FrozenErr::new(1, 2, 3, b"io", b"");
        assert_eq!(err.context, "[io] ");
    }

    #[test]
    fn ok_empty_detail() {
        let err = FrozenErr::new(1, 2, 3, b"", b"failure");
        assert_eq!(err.context, "[] failure");
    }

    #[test]
    fn ok_error_id_roundtrip_basic() {
        let err = FrozenErr::new(0x01, 0x02, 0x0033, b"io", b"read failed");
        let (m, d, r) = from_error_id(err.id);

        assert_eq!(err.id, 0x0102_0033);
        assert_eq!((m, d, r), (0x01, 0x02, 0x0033));
    }

    #[test]
    fn ok_new_and_new_raw_same_id() {
        let e1 = FrozenErr::new(1, 2, 3, b"io", b"fail");

        let io_err = std::io::Error::new(std::io::ErrorKind::Other, "fail");
        let e2 = FrozenErr::new_raw(1, 2, 3, b"io", io_err);

        assert_eq!(e1.id, e2.id);
    }

    #[test]
    fn ok_error_id_roundtrip_edges() {
        let err = FrozenErr::new(0xff, 0x00, 0xffff, b"edge", b"max values");
        let (m, d, r) = from_error_id(err.id);

        assert_eq!(err.id, 0xff00_ffff);
        assert_eq!((m, d, r), (0xff, 0x00, 0xffff));
    }

    #[test]
    fn ok_error_id_reason_only_changes_low_bits() {
        let e1 = FrozenErr::new(1, 2, 1, b"x", b"a");
        let e2 = FrozenErr::new(1, 2, 2, b"x", b"a");

        assert_eq!(e1.id & 0xffff_0000, e2.id & 0xffff_0000);
        assert_ne!(e1.id & 0x0000_ffff, e2.id & 0x0000_ffff);
    }

    #[test]
    fn ok_context_formatting() {
        let err = FrozenErr::new(1, 1, 1, b"io", b"disk failure");
        assert_eq!(err.context, "[io] disk failure");
    }

    #[test]
    fn ok_new_raw_uses_display() {
        let io_err = std::io::Error::new(std::io::ErrorKind::PermissionDenied, "access denied");
        let err = FrozenErr::new_raw(1, 2, 3, b"io", io_err);

        assert!(err.context.contains("[io]"));
        assert!(err.context.contains("access denied"));
    }

    #[test]
    fn ok_compare_same_id_different_context() {
        let e1 = FrozenErr::new(1, 2, 3, b"io", b"a");
        let e2 = FrozenErr::new(1, 2, 3, b"io", b"b");

        assert!(e1.compare_id(&e2));
    }

    #[test]
    fn ok_compare_different_id() {
        let e1 = FrozenErr::new(1, 2, 3, b"io", b"a");
        let e2 = FrozenErr::new(1, 2, 4, b"io", b"a");

        assert!(!e1.compare_id(&e2));
    }
}
