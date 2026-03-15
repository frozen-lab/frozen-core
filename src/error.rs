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
//! use frozen_core::error::{FrozenErr, FrozenRes, ErrCode};
//!
//! fn read_file() -> FrozenRes<()> {
//!     Err(FrozenErr::new(1, 2, ErrCode::new(0x0033, "io"), "read failed"))
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
    /// use frozen_core::error::{FrozenErr, ErrCode};
    ///
    /// let err = FrozenErr::new(1, 2, ErrCode::new(0x0033, "io"), "failed to read file");
    ///
    /// assert_eq!(err.id, 0x0102_0033);
    /// assert!(err.context.contains("[io]"));
    /// assert!(err.context.contains("failed to read file"));
    /// ```
    #[inline(always)]
    pub fn new(module: u8, domain: u8, code: ErrCode, errmsg: &str) -> Self {
        Self {
            id: error_id(module, domain, code.reason),
            context: format!("[{}] {}", code.detail, errmsg),
        }
    }

    /// Construct a new [`FrozenErr`] from raw [`Error`] object
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::{FrozenErr, ErrCode};
    ///
    /// let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "file missing");
    /// let err = FrozenErr::new_raw(1, 2, ErrCode::new(0x0033, "io"), io_err);
    ///
    /// assert_eq!(err.id, 0x0102_0033);
    /// assert!(err.context.contains("[io]"));
    /// assert!(err.context.contains("file missing"));
    /// ```
    #[inline(always)]
    pub fn new_raw<E: std::fmt::Display>(module: u8, domain: u8, code: ErrCode, err: E) -> Self {
        Self {
            id: error_id(module, domain, code.reason),
            context: format!("[{}] {}", code.detail, err.to_string()),
        }
    }

    /// Compare two errors by their encoded id's
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::{FrozenErr, ErrCode};
    ///
    /// let err1 = FrozenErr::new(0, 0, ErrCode::new(0x30, "test"), "something failed");
    /// let err2 = FrozenErr::new(0, 0, ErrCode::new(0x30, "test"), "another message");
    ///
    /// assert!(err1.compare_id(&err2));
    /// ```
    #[inline(always)]
    pub fn compare_id(&self, err: &FrozenErr) -> bool {
        self.id == err.id
    }
}

/// Static error descriptor used to construct [`FrozenErr`]
///
/// ## Example
///
/// ```
/// use frozen_core::error::ErrCode;
///
/// const LOCK_ERR: ErrCode = frozen_core::error::ErrCode::new(0x300, "lock error");
///
/// assert_eq!(LOCK_ERR.reason, 0x300);
/// assert_eq!(LOCK_ERR.detail, "lock error");
/// ```
#[derive(Debug, Clone)]
pub struct ErrCode {
    /// 16-bit reason code encoded into [`FrozenErr::id`]
    pub reason: u16,

    /// Short subsystem label included in the formatted error context
    pub detail: &'static str,
}

impl ErrCode {
    /// Create a new [`ErrCode`]
    ///
    /// *NOTE:* This function is `const`, allowing error codes to be defined as compile-time constants
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::ErrCode;
    ///
    /// const LOCK_ERR: ErrCode = frozen_core::error::ErrCode::new(0x300, "lock error");
    ///
    /// assert_eq!(LOCK_ERR.reason, 0x300);
    /// assert_eq!(LOCK_ERR.detail, "lock error");
    /// ```
    #[inline]
    pub const fn new(reason: u16, detail: &'static str) -> Self {
        Self { reason, detail }
    }
}

#[inline]
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
        let err = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "failure");
        assert_eq!(err.context, "[io] failure");
    }

    #[test]
    fn ok_empty_message() {
        let err = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "");
        assert_eq!(err.context, "[io] ");
    }

    #[test]
    fn ok_empty_detail() {
        let err = FrozenErr::new(1, 2, ErrCode::new(3, ""), "failure");
        assert_eq!(err.context, "[] failure");
    }

    #[test]
    fn ok_error_id_roundtrip_basic() {
        let err = FrozenErr::new(0x01, 0x02, ErrCode::new(0x0033, "io"), "read failed");
        let (m, d, r) = from_error_id(err.id);

        assert_eq!(err.id, 0x0102_0033);
        assert_eq!((m, d, r), (0x01, 0x02, 0x0033));
    }

    #[test]
    fn ok_new_and_new_raw_same_id() {
        let e1 = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "fail");

        let io_err = std::io::Error::new(std::io::ErrorKind::Other, "fail");
        let e2 = FrozenErr::new_raw(1, 2, ErrCode::new(3, "io"), io_err);

        assert_eq!(e1.id, e2.id);
    }

    #[test]
    fn ok_error_id_roundtrip_edges() {
        let err = FrozenErr::new(0xff, 0x00, ErrCode::new(0xffff, "edge"), "max values");
        let (m, d, r) = from_error_id(err.id);

        assert_eq!(err.id, 0xff00_ffff);
        assert_eq!((m, d, r), (0xff, 0x00, 0xffff));
    }

    #[test]
    fn ok_error_id_reason_only_changes_low_bits() {
        let e1 = FrozenErr::new(1, 2, ErrCode::new(1, "x"), "a");
        let e2 = FrozenErr::new(1, 2, ErrCode::new(2, "x"), "a");

        assert_eq!(e1.id & 0xffff_0000, e2.id & 0xffff_0000);
        assert_ne!(e1.id & 0x0000_ffff, e2.id & 0x0000_ffff);
    }

    #[test]
    fn ok_context_formatting() {
        let err = FrozenErr::new(1, 1, ErrCode::new(1, "io"), "disk failure");
        assert_eq!(err.context, "[io] disk failure");
    }

    #[test]
    fn ok_new_raw_uses_display() {
        let io_err = std::io::Error::new(std::io::ErrorKind::PermissionDenied, "access denied");
        let err = FrozenErr::new_raw(1, 2, ErrCode::new(3, "io"), io_err);

        assert!(err.context.contains("[io]"));
        assert!(err.context.contains("access denied"));
    }

    #[test]
    fn ok_compare_same_id_different_context() {
        let e1 = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "a");
        let e2 = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "b");

        assert!(e1.compare_id(&e2));
    }

    #[test]
    fn ok_compare_different_id() {
        let e1 = FrozenErr::new(1, 2, ErrCode::new(3, "io"), "a");
        let e2 = FrozenErr::new(1, 2, ErrCode::new(4, "io"), "a");

        assert!(!e1.compare_id(&e2));
    }
}
