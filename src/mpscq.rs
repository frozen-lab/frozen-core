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
    /// Check if the [`MPSCQueue`] is currently empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.head.load(atomic::Ordering::Acquire).is_null()
    }

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;

    mod basics {
        use super::*;

        #[test]
        fn ok_push_drain_single() {
            let q = MPSCQueue::default();
            q.push(1usize);

            let batch = q.drain();
            assert_eq!(batch, vec![1]);
        }

        #[test]
        fn ok_push_drain_multiple() {
            let q = MPSCQueue::default();

            q.push(1);
            q.push(2);
            q.push(3);

            let batch = q.drain();
            assert_eq!(batch.len(), 3);
            assert_eq!(batch, vec![3, 2, 1]);
        }

        #[test]
        fn ok_drain_empty_when_queue_empty() {
            let q: MPSCQueue<usize> = MPSCQueue::default();
            let batch = q.drain();
            assert!(batch.is_empty());
        }
    }

    mod empty {
        use super::*;

        #[test]
        fn ok_is_empty_true_on_init() {
            let q: MPSCQueue<usize> = MPSCQueue::default();
            assert!(q.is_empty());
        }

        #[test]
        fn ok_is_empty_false_after_push() {
            let q = MPSCQueue::default();
            q.push(1);
            assert!(!q.is_empty());
        }

        #[test]
        fn ok_is_empty_true_after_drain() {
            let q = MPSCQueue::default();

            q.push(1);
            q.push(2);

            let _ = q.drain();
            assert!(q.is_empty());
        }
    }

    mod cycles {
        use super::*;

        #[test]
        fn ok_single_push_drain_cycles() {
            let q = MPSCQueue::default();
            for i in 0..0x400 {
                q.push(i);
                let batch = q.drain();

                assert_eq!(batch.len(), 1);
                assert_eq!(batch[0], i);
            }
        }

        #[test]
        fn ok_multi_push_drain_cycles() {
            let q = MPSCQueue::default();
            for _ in 0..0x200 {
                for i in 0..0x0A {
                    q.push(i);
                }

                let batch = q.drain();
                assert_eq!(batch.len(), 0x0A);
            }
        }
    }

    mod concurrency {
        use super::*;

        const THREADS: usize = 0x0A;
        const ITERS: usize = 0x2000;

        #[test]
        fn ok_multi_tx_push() {
            let q = Arc::new(MPSCQueue::default());

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let q = q.clone();
                handles.push(thread::spawn(move || {
                    for i in 0..ITERS {
                        q.push(i);
                    }
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let batch = q.drain();
            assert_eq!(batch.len(), THREADS * ITERS);
        }

        #[test]
        fn ok_multi_tx_push_high_contention() {
            let q = Arc::new(MPSCQueue::default());
            let barrier = Arc::new(Barrier::new(THREADS * 2));

            let mut handles = Vec::new();

            for _ in 0..(THREADS * 2) {
                let q = q.clone();
                let barrier = barrier.clone();

                handles.push(thread::spawn(move || {
                    barrier.wait();

                    for i in 0..(ITERS * 2) {
                        q.push(i);
                    }
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let batch = q.drain();
            assert_eq!(batch.len(), (THREADS * 2) * (ITERS * 2));
        }

        #[test]
        fn ok_multi_tx_push_drain() {
            let q = Arc::new(MPSCQueue::default());
            let producer = {
                let q = q.clone();
                thread::spawn(move || {
                    for i in 0..0x8000 {
                        q.push(i);
                    }
                })
            };

            let consumer = {
                let q = q.clone();
                thread::spawn(move || {
                    let mut total = 0usize;
                    while total < 0x8000 {
                        let batch = q.drain();
                        total += batch.len();
                    }

                    total
                })
            };

            producer.join().unwrap();
            let total = consumer.join().unwrap();

            assert_eq!(total, 0x8000);
        }
    }
}
