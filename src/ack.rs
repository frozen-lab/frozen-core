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
use event_listener::{Event, EventListener, Listener};
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
    event: Event,
}

impl Default for Completion {
    fn default() -> Self {
        Self {
            current_epoch: atomic::AtomicU64::new(0),
            durable_epoch: atomic::AtomicU64::new(0),
            error: AckError::default(),
            event: Event::new(),
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
    listener: Option<EventListener>,
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

    /// Blocks the current thread unitl the [`AckTicket`] becomes durable
    ///
    /// If a durability error is reported before the epoch becomes durable, the corresponding
    /// [`FrozenError`] is returned instead.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ack::{AckTicket, Completion};
    /// use std::{sync::Arc, thread, time};
    ///
    /// let completion = Arc::new(Completion::default());
    /// let epoch = completion.increment_current_epoch();
    /// let ticket = AckTicket::new(epoch, completion.clone());
    ///
    /// thread::spawn({
    ///     let completion = completion.clone();
    ///
    ///     move || {
    ///         thread::sleep(time::Duration::from_millis(10));
    ///         completion.mark_epoch_as_durable(epoch);
    ///         completion.notify_all_listeners();
    ///     }
    /// });
    ///
    /// assert_eq!(ticket.wait().unwrap(), epoch);
    /// ```
    #[inline(always)]
    pub fn wait(&self) -> FrozenResult<TEpoch> {
        loop {
            if self.is_ready() {
                return Ok(self.epoch);
            }

            if let Some(frozen_err) = self.completion.get_err() {
                return Err(frozen_err);
            }

            let listener = self.completion.event.listen();

            if self.is_ready() {
                return Ok(self.epoch);
            }

            if let Some(err) = self.completion.get_err() {
                return Err(err);
            }

            listener.wait();
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::ErrCode;
    use std::{sync, thread, time};

    mod completion {
        use super::*;

        #[test]
        fn ok_increment_current_epoch() {
            let completion = Completion::default();

            assert_eq!(completion.increment_current_epoch(), 1);
            assert_eq!(completion.increment_current_epoch(), 2);
            assert_eq!(completion.increment_current_epoch(), 3);
        }

        #[test]
        fn ok_mark_epoch_as_durable() {
            let completion = Completion::default();
            completion.mark_epoch_as_durable(0x0C);

            assert_eq!(completion.read_durable_epoch(), 0x0C);
        }

        #[test]
        fn ok_set_get_err() {
            let completion = Completion::default();
            let err = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure");
            completion.set_err(err.clone());

            assert_eq!(completion.get_err(), Some(err));
        }

        #[test]
        fn ok_del_err() {
            let completion = Completion::default();

            completion.set_err(FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure"));
            assert!(completion.get_err().is_some());

            completion.del_err();
            assert!(completion.get_err().is_none());
        }

        #[test]
        fn ok_set_err_overwrites_previous() {
            let completion = Completion::default();

            let err_1 = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "first");
            let err_2 = FrozenError::new(0x11, 0x21, ErrCode::new(0x31, "sync"), "second");

            completion.set_err(err_1);
            completion.set_err(err_2.clone());

            assert_eq!(completion.get_err(), Some(err_2));
        }
    }

    mod ack_ticket {
        use super::*;

        #[test]
        fn ok_new() {
            let completion = sync::Arc::new(Completion::default());
            let ticket = AckTicket::new(0x23, completion);

            assert_eq!(ticket.epoch(), 0x23);
        }

        #[test]
        fn ok_await_when_epoch_already_durable() {
            let completion = sync::Arc::new(Completion::default());
            completion.mark_epoch_as_durable(0x0A);

            let ticket = AckTicket::new(0x0A, completion);
            let durable_epoch = futures::executor::block_on(ticket).expect("ticket must complete");

            assert_eq!(durable_epoch, 0x0A);
        }

        #[test]
        fn ok_await_after_durability_progress() {
            let completion = sync::Arc::new(Completion::default());
            let ticket = AckTicket::new(1, completion.clone());

            thread::spawn({
                let completion = completion.clone();

                move || {
                    thread::sleep(time::Duration::from_millis(0x0A));

                    completion.mark_epoch_as_durable(1);
                    completion.notify_all_listeners();
                }
            });

            let durable_epoch = futures::executor::block_on(ticket).expect("ticket must complete");

            assert_eq!(durable_epoch, 1);
        }

        #[test]
        fn err_await_when_error_is_present() {
            let completion = sync::Arc::new(Completion::default());
            let expected_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure");

            completion.set_err(expected_error.clone());

            let ticket = AckTicket::new(1, completion);
            let err = futures::executor::block_on(ticket).expect_err("ticket must fail");

            assert_eq!(err, expected_error);
        }

        #[test]
        fn err_await_when_error_arrives_later() {
            let completion = sync::Arc::new(Completion::default());
            let ticket = AckTicket::new(1, completion.clone());
            let expected_error = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure");

            thread::spawn({
                let completion = completion.clone();
                let expected_error = expected_error.clone();

                move || {
                    thread::sleep(time::Duration::from_millis(0x0A));

                    completion.set_err(expected_error);
                    completion.notify_all_listeners();
                }
            });

            let err = futures::executor::block_on(ticket).expect_err("ticket must fail");
            assert_eq!(err, expected_error);
        }

        #[test]
        fn ok_multiple_tickets_waiting_for_same_epoch() {
            let completion = sync::Arc::new(Completion::default());

            let ticket_1 = AckTicket::new(1, completion.clone());
            let ticket_2 = AckTicket::new(1, completion.clone());
            let ticket_3 = AckTicket::new(1, completion.clone());

            thread::spawn({
                let completion = completion.clone();
                move || {
                    thread::sleep(time::Duration::from_millis(0x0A));

                    completion.mark_epoch_as_durable(1);
                    completion.notify_all_listeners();
                }
            });

            assert_eq!(futures::executor::block_on(ticket_1).expect("ticket_1 must complete"), 1);
            assert_eq!(futures::executor::block_on(ticket_2).expect("ticket_2 must complete"), 1);
            assert_eq!(futures::executor::block_on(ticket_3).expect("ticket_3 must complete"), 1);
        }

        #[test]
        fn ok_multiple_epochs_complete_in_order() {
            let completion = sync::Arc::new(Completion::default());

            let ticket_1 = AckTicket::new(1, completion.clone());
            let ticket_2 = AckTicket::new(2, completion.clone());
            let ticket_3 = AckTicket::new(3, completion.clone());

            completion.mark_epoch_as_durable(3);

            assert_eq!(futures::executor::block_on(ticket_1).expect("ticket_1 must complete"), 1);
            assert_eq!(futures::executor::block_on(ticket_2).expect("ticket_2 must complete"), 2);
            assert_eq!(futures::executor::block_on(ticket_3).expect("ticket_3 must complete"), 3);
        }
    }

    mod ticket_wait {
        use super::*;

        #[test]
        fn ok_wait_when_epoch_already_durable() {
            let completion = sync::Arc::new(Completion::default());
            completion.mark_epoch_as_durable(1);

            let ticket = AckTicket::new(1, completion);
            assert_eq!(ticket.wait().expect("ticket must complete"), 1);
        }

        #[test]
        fn ok_wait_after_durability_progress() {
            let completion = sync::Arc::new(Completion::default());
            let ticket = AckTicket::new(1, completion.clone());

            thread::spawn({
                let completion = completion.clone();
                move || {
                    thread::sleep(time::Duration::from_millis(10));

                    completion.mark_epoch_as_durable(1);
                    completion.notify_all_listeners();
                }
            });

            assert_eq!(ticket.wait().expect("ticket must complete"), 1);
        }

        #[test]
        fn err_wait_when_error_is_present() {
            let completion = sync::Arc::new(Completion::default());
            let expected = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure");

            completion.set_err(expected.clone());

            let ticket = AckTicket::new(1, completion);
            assert_eq!(ticket.wait().expect_err("ticket must fail"), expected);
        }

        #[test]
        fn err_wait_when_error_arrives_later() {
            let completion = sync::Arc::new(Completion::default());
            let ticket = AckTicket::new(1, completion.clone());
            let expected = FrozenError::new(0x10, 0x20, ErrCode::new(0x30, "io"), "failure");

            thread::spawn({
                let completion = completion.clone();
                let expected = expected.clone();

                move || {
                    thread::sleep(time::Duration::from_millis(10));

                    completion.set_err(expected);
                    completion.notify_all_listeners();
                }
            });

            assert_eq!(ticket.wait().expect_err("ticket must fail"), expected);
        }
    }
}
