//! A lock-free multi-producer single-consumer queue
//!
//! ## Ownership of `T`
//!
//! When [`MPSCQueue::push`] is called, the ownership of `T` is moved into the queue, and when [`MPSCQueue::drain()`]
//! is called, the ownership is moved back to the caller, via the returned `Vec<T>`, the queue itself never drops `T`
//! during normal ops; the caller decides when the drained values are dropped
//!
//! ## MPSC Model
//!
//! By design [`MPSCQueue::drain`] is thread safe, but calling it from multiple threads is semantically incorrect, as in
//! the MPSC model there should only be a single consumer, while there can be many producers,
//!
//! - Many tx can call [`MPSCQueue::push`]
//! - Only a single tx should call [`MPSCQueue::drain`]
//!
//! ## Example
//!
//! ```
//! let queue = frozen_core::mpscq::MPSCQueue::<usize>::default();
//!
//! queue.push(1usize);
//! queue.push(2usize);
//!
//! let batch = queue.drain();
//! assert_eq!(batch.len(), 2);
//!
//! drop(batch); // values is dropped here
//! ```

use core::{ptr, sync::atomic};

/// A lock-free multi-producer single-consumer queue
///
/// ## Example
///
/// ```
/// let queue = frozen_core::mpscq::MPSCQueue::<usize>::default();
///
/// queue.push(1usize);
/// queue.push(2usize);
///
/// let batch = queue.drain();
/// assert_eq!(batch, vec![2usize, 1usize]);
///
/// drop(batch); // values is dropped here
/// ```
#[derive(Debug)]
pub struct MPSCQueue<T> {
    head: atomic::AtomicPtr<Node<T>>,
}

impl<T> MPSCQueue<T> {
    /// Push an entry into the [`MPSCQueue`]
    ///
    /// ## Ordering
    ///
    /// The queue internally uses a linked list, therefore entries are stored in last-in-first-out (LIFO) order
    ///
    /// ## Example
    ///
    /// ```
    /// let queue = frozen_core::mpscq::MPSCQueue::<usize>::default();
    /// queue.push(1usize);
    ///
    /// let batch = queue.drain();
    /// assert_eq!(batch.len(), 1);
    ///
    /// drop(batch); // values is dropped here
    /// ```
    #[inline(always)]
    pub fn push(&self, value: T) {
        let mut head = self.head.load(atomic::Ordering::Relaxed);
        let node = Node::new(value);

        loop {
            unsafe { (*node).next = head };

            match self
                .head
                .compare_exchange_weak(head, node, atomic::Ordering::AcqRel, atomic::Ordering::Relaxed)
            {
                Ok(_) => return,
                Err(h) => head = h,
            }
        }
    }

    /// Drain a batch of entries from [`MPSCQueue`]
    ///
    /// ## Ordering
    ///
    /// The queue internally behaves like a stack, therefore entries are returned in last-in-first-out (LIFO)
    /// order when drained
    ///
    /// ## Example
    ///
    /// ```
    /// let queue = frozen_core::mpscq::MPSCQueue::<usize>::default();
    ///
    /// queue.push(1usize);
    /// queue.push(2usize);
    /// queue.push(3usize);
    ///
    /// let batch = queue.drain();
    ///
    /// assert_eq!(batch.len(), 3);
    /// assert_eq!(batch, vec![3usize, 2usize, 1usize]);
    ///
    /// drop(batch); // values is dropped here
    /// ```
    #[inline(always)]
    pub fn drain(&self) -> Vec<T> {
        let mut out = Vec::new();
        let mut node = self.head.swap(ptr::null_mut(), atomic::Ordering::AcqRel);

        while !node.is_null() {
            let boxed = unsafe { Box::from_raw(node) };
            node = boxed.next;
            out.push(boxed.value);
        }

        out
    }
}

impl<T> Default for MPSCQueue<T> {
    fn default() -> Self {
        Self {
            head: atomic::AtomicPtr::new(ptr::null_mut()),
        }
    }
}

impl<T> Drop for MPSCQueue<T> {
    fn drop(&mut self) {
        let mut node = self.head.swap(ptr::null_mut(), atomic::Ordering::Relaxed);
        while !node.is_null() {
            unsafe {
                let boxed = Box::from_raw(node);
                node = boxed.next;
            }
        }
    }
}

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

impl<T> Node<T> {
    fn new(value: T) -> *mut Self {
        Box::into_raw(Box::new(Self {
            next: ptr::null_mut(),
            value,
        }))
    }
}
