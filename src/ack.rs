//! Acknowledge primitives for durability tracking
//!
//! In our storage system, an acknowledgement represents the eventual durability state of
//! previously submitted write operation.
//!
//! ## Example
//!
//! ```
//! use frozen_core::ack::{AckTicket, Completion};
//! use std::sync::Arc;
//!
//! let completion = Arc::new(Completion::default());
//!
//! let epoch = completion.increment_current_epoch();
//! let ticket = AckTicket::new(epoch, completion.clone());
//!
//! completion.mark_epoch_as_durable(epoch);
//! completion.notify_all_listeners();
//!
//! let durable_epoch = futures::executor::block_on(ticket).unwrap();
//! assert_eq!(durable_epoch, epoch);
//! ```

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

/// A shared durability acknowledgement state used for issuing [`AckTicket`]'s
///
/// The completion state tracks following things:
///
/// * The latest assigned epoch
/// * The latest durable epoch
/// * Waiters blocked on durability advancement
/// * Durability errors (if any) blocking durability progress
///
/// ## Example
///
/// ```
/// use frozen_core::ack::Completion;
///
/// let completion = Completion::default();
///
/// assert_eq!(completion.read_current_epoch(), 0);
/// assert_eq!(completion.read_durable_epoch(), 0);
/// ```
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
    /// Advance current and return next durability epoch
    ///
    /// *NOTE:* Epoch value is monotonically increasing and used to identify unique write
    /// operations.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    ///
    /// assert_eq!(completion.increment_current_epoch(), 1);
    /// assert_eq!(completion.increment_current_epoch(), 2);
    /// assert_eq!(completion.increment_current_epoch(), 3);
    /// ```
    #[inline]
    pub fn increment_current_epoch(&self) -> TEpoch {
        self.current_epoch.fetch_add(1, atomic::Ordering::AcqRel).wrapping_add(1)
    }

    /// Mark given [`TEpoch`] as durable
    ///
    /// *NOTE:* Once an epoch is marked durable, all earlier epochs are implicitly understood to be
    /// durable.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    /// completion.mark_epoch_as_durable(0x0A);
    ///
    /// assert_eq!(completion.read_durable_epoch(), 0x0A);
    /// ```
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

    /// Read the latest assigned epoch
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    /// completion.increment_current_epoch();
    ///
    /// assert_eq!(completion.read_current_epoch(), 1);
    /// ```
    #[inline]
    pub fn read_current_epoch(&self) -> TEpoch {
        self.current_epoch.load(atomic::Ordering::Acquire)
    }

    /// Read the latest durable epoch
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    /// completion.mark_epoch_as_durable(0x3A);
    ///
    /// assert_eq!(completion.read_durable_epoch(), 0x3A);
    /// ```
    #[inline]
    pub fn read_durable_epoch(&self) -> TEpoch {
        self.durable_epoch.load(atomic::Ordering::Acquire)
    }

    /// Wake all the listeners currently waiting for durability progress
    ///
    /// *NOTE:* Waking listeners does not modify any durable state and are typically called after
    /// advancing the durable epoch or after occurence of [`AckError`].
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::Completion;
    ///
    /// let completion = Completion::default();
    /// completion.notify_all_listeners();
    /// ```
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
    /// Construct a new [`AckTicket`] for a write operation
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::{AckTicket, Completion};
    /// use std::sync::Arc;
    ///
    /// let completion = Arc::new(Completion::default());
    /// let ticket = AckTicket::new(1, completion);
    ///
    /// assert_eq!(ticket.epoch(), 1);
    /// ```
    #[inline]
    pub const fn new(epoch: TEpoch, completion: sync::Arc<Completion>) -> Self {
        Self { epoch, completion, listener: None }
    }

    /// Read assigned durability epoch for the [`AckTicket`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::{AckTicket, Completion};
    /// use std::sync::Arc;
    ///
    /// let completion = Arc::new(Completion::default());
    /// let ticket = AckTicket::new(0x4C, completion);
    ///
    /// assert_eq!(ticket.epoch(), 0x4C);
    /// ```
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
