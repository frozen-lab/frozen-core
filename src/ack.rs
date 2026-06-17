//! Acknowledge primitives for durability tracking
//!
//! In storage system an acknowledgement is a confirmation that a previously submitted operations
//! has reached a durable state.

use crate::{error::FrozenError, hints};
use std::{ptr, sync::atomic};

/// A monotomically increasing epoch used as indentifier for tracking durability of write operations
pub type EPOCH = u64;

#[derive(Debug)]
struct AckError(atomic::AtomicPtr<FrozenError>);

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

///
#[derive(Debug)]
pub struct Completion {
    current_epoch: atomic::AtomicU64,
    durable_epoch: atomic::AtomicU64,
    error: AckError,
    event: event_listener::Event,
}

impl Default for Completion {
    fn default() -> Self {
        Self {
            current_epoch: atomic::AtomicU64::new(0),
            durable_epoch: atomic::AtomicU64::new(0),
            error: AckError::default(),
            event: event_listener::Event::new(),
        }
    }
}

impl Completion {
    ///
    #[inline]
    pub fn increment_current_epoch(&self) -> EPOCH {
        self.current_epoch.fetch_add(1, atomic::Ordering::AcqRel).wrapping_add(1)
    }

    ///
    #[inline]
    pub fn mark_epoch_as_durable(&self, epoch: EPOCH) {
        self.durable_epoch.store(epoch, atomic::Ordering::Release);
        self.event.notify(usize::MAX);
    }

    /// Fetch the acknowledgement error (if any)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    /// assert_eq!(completion.get_err(), None);
    /// ```
    #[inline]
    pub fn get_err(&self) -> Option<FrozenError> {
        let curr_err = self.error.0.load(atomic::Ordering::Acquire);
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
    /// use frozen_core::{ack::Completion, error::{FrozenError, ErrCode}};
    ///
    /// let completion = Completion::default();
    /// let new_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failed to read file");
    ///
    /// completion.set_err(new_error.clone());
    /// assert_eq!(completion.get_err(), Some(new_error));
    /// ```
    #[inline]
    pub fn set_err(&self, new_error: FrozenError) {
        let boxed_error = Box::into_raw(Box::new(new_error));
        let old_err = self.error.0.swap(boxed_error, atomic::Ordering::AcqRel);

        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }

    /// Clear acknowledgement error by replacing the underying error w/ an empty pointer
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{ack::Completion, error::{FrozenError, ErrCode}};
    ///
    /// let completion = Completion::default();
    /// let new_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failed to read file");
    ///
    /// completion.set_err(new_error.clone());
    /// assert!(completion.get_err().is_some());
    ///
    /// completion.del_err();
    /// assert!(completion.get_err().is_none());
    /// ```
    #[inline]
    pub fn del_err(&self) {
        let old_err = self.error.0.swap(ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old_err.is_null()) {
            let _ = unsafe { Box::from_raw(old_err) };
        }
    }

    ///
    #[inline]
    pub fn read_current_epoch(&self) -> EPOCH {
        self.current_epoch.load(atomic::Ordering::Acquire)
    }

    ///
    #[inline]
    pub fn read_durable_epoch(&self) -> EPOCH {
        self.durable_epoch.load(atomic::Ordering::Acquire)
    }
}
