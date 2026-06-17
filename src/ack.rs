//! Acknowledge primitives for durability tracking
//!
//! In storage system an acknowledgement is a confirmation that a previously submitted operations
//! has reached a durable state.

use crate::{error::FrozenError, hints};
use std::{ptr, sync::atomic};

/// A monotomically increasing epoch used as indentifier for tracking durability of write operations
pub type EPOCH = u64;

/// Stores [`FrozenError`] related to acknowledgement of durability
///
/// ## Example
///
/// ```
/// use frozen_core::ack::AckError;
///
/// let error = AckError::default();
/// assert_eq!(error.get(), None);
/// ```
#[derive(Debug)]
pub struct AckError(atomic::AtomicPtr<FrozenError>);

impl Default for AckError {
    fn default() -> Self {
        Self(atomic::AtomicPtr::new(ptr::null_mut()))
    }
}

impl Drop for AckError {
    fn drop(&mut self) {
        let err_ptr = self.0.load(atomic::Ordering::Acquire);
        if !err_ptr.is_null() {
            let _ = unsafe { Box::from_raw(err_ptr) };
        }
    }
}

impl AckError {
    /// Fetch the acknowledgement error (if any)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::AckError;
    ///
    /// let error = AckError::default();
    /// assert_eq!(error.get(), None);
    /// ```
    #[inline]
    pub fn get(&self) -> Option<FrozenError> {
        let curr_err = self.0.load(atomic::Ordering::Acquire);
        if hints::unlikely(!curr_err.is_null()) {
            let frozen_error = unsafe { (*curr_err).clone() };
            return Some(frozen_error);
        }

        None
    }

    /// Update current acknowledgement error w/ a new [`FrozenError`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{ack::AckError, error::{FrozenError, ErrCode}};
    ///
    /// let ack_error = AckError::default();
    /// let new_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failed to read file");
    ///
    /// ack_error.set(new_error.clone());
    /// assert_eq!(ack_error.get(), Some(new_error));
    /// ```
    #[inline]
    pub fn set(&self, new_error: FrozenError) {
        let boxed_error = Box::into_raw(Box::new(new_error));
        let old_err = self.0.swap(boxed_error, atomic::Ordering::AcqRel);

        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }

    /// Clear acknowledgement error by replacing the underying error w/ an empty pointer
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{ack::AckError, error::{FrozenError, ErrCode}};
    ///
    /// let ack_error = AckError::default();
    /// let new_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failed to read file");
    ///
    /// ack_error.set(new_error.clone());
    /// assert!(ack_error.get().is_some());
    ///
    /// ack_error.del();
    /// assert!(ack_error.get().is_none());
    /// ```
    #[inline]
    pub fn del(&self) {
        let old_err = self.0.swap(ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }
}
