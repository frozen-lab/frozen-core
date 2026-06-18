//! Acknowledge primitives for durability tracking
//!
//! In storage system an acknowledgement is a confirmation that a previously submitted operations
//! has reached a durable state.

use crate::{
    error::{FrozenError, FrozenResult},
    hints,
};
use std::{future, pin, ptr, sync, sync::atomic, task};

/// A monotomically increasing epoch used as indentifier for tracking durability of write operations
pub type TEpoch = u64;

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
    pub fn increment_current_epoch(&self) -> TEpoch {
        self.current_epoch.fetch_add(1, atomic::Ordering::AcqRel).wrapping_add(1)
    }

    ///
    #[inline]
    pub fn mark_epoch_as_durable(&self, epoch: TEpoch) {
        self.durable_epoch.store(epoch, atomic::Ordering::Release);
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
    pub fn read_current_epoch(&self) -> TEpoch {
        self.current_epoch.load(atomic::Ordering::Acquire)
    }

    ///
    #[inline]
    pub fn read_durable_epoch(&self) -> TEpoch {
        self.durable_epoch.load(atomic::Ordering::Acquire)
    }

    ///
    #[inline]
    pub fn notify_all_listeners(&self) {
        self.event.notify(usize::MAX);
    }
}

/// Durability handle associated with the write operation
///
/// ## Epoch
///
/// Every ticket is assigned a monotonically increasing epoch to moniter durability
///
/// ## Durability Guarantee
///
/// If wanted, the ticket could be awaited to poll till the epoch becomes durable.
///
/// Once a await on ticket is completed successfully, all writes assigned to earlier epochs are
/// also guaranteed to be durable.
///
/// *NOTE:* Using `await` is optional. Callers that only require fire-and-forget semantics may
/// simply discard the returned ticket.
#[derive(Debug)]
pub struct AckTicket {
    epoch: TEpoch,
    completion: sync::Arc<Completion>,
    listener: Option<event_listener::EventListener>,
}

impl AckTicket {
    /// Construct a new [`AckTicket`]
    #[inline]
    pub const fn new(epoch: TEpoch, completion: sync::Arc<Completion>) -> Self {
        Self { epoch, completion, listener: None }
    }

    /// Read assigned durability epoch for the [`AckTicket`]
    #[inline(always)]
    pub const fn epoch(&self) -> TEpoch {
        self.epoch
    }

    #[inline]
    fn is_ready(&self) -> bool {
        self.completion.read_durable_epoch() >= self.epoch
    }
}

impl future::Future for AckTicket {
    type Output = FrozenResult<TEpoch>;

    fn poll(mut self: pin::Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Self::Output> {
        loop {
            if self.is_ready() {
                return task::Poll::Ready(Ok(self.epoch));
            }

            if let Some(frozen_err) = self.completion.get_err() {
                return task::Poll::Ready(Err(frozen_err));
            }

            if self.listener.is_none() {
                self.listener = Some(self.completion.event.listen());

                // NOTE: prevent lost wakeups
                continue;
            }

            let listener = self.listener.as_mut().unwrap();
            match pin::Pin::new(listener).poll(cx) {
                task::Poll::Ready(()) => {
                    self.listener = None;

                    // NOTE: Re-check durable epoch & error
                    continue;
                }

                task::Poll::Pending => {
                    return task::Poll::Pending;
                }
            }
        }
    }
}
