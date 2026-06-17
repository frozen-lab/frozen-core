//! A low-latency implementation of MPSC (multi-producer single-consumer) queue
//!
//! ## Benchmarks
//!
//! Observed latency for push and drain operations,
//!
//! _NOTE:_ All measurements include end-to-end operation cost (incl. allocations & deallocation)
//!
//! ```md
//! | Operation | Latency (average)  |
//! |:----------|:-------------------|
//! | Push      | ~36 nanoseconds    |
//! | Drain     | ~37 nanoseconds    |
//! ```
//!
//! Environment used for benching,
//!
//! * OS: NixOS (WSL2)
//! * Architecture: x86_64
//! * Memory: 8 GiB RAM (DDR4)
//! * Rust: rustc 1.86.0 w/ cargo 1.86.0
//! * Kernel: Linux 6.6.87.2-microsoft-standard-WSL2
//! * CPU: Intel® Core™ i5-10300H @ 2.50GHz (4C / 8T)
//!
//! ## Example
//!
//! ```
//! use frozen_core::mpscq::MPSCQueue;
//!
//! let queue = MPSCQueue::<usize>::default();
//!
//! queue.push(0x10);
//! queue.push(0x20);
//!
//! let batch: Vec<usize> = queue.drain();
//! assert_eq!(batch.len(), 2);
//! ```

use core::{ptr, sync::atomic};

/// A low-latency implementation of MPSC (multi-producer single-consumer) queue
///
/// ## Example
///
/// ```
/// use frozen_core::mpscq::MPSCQueue;
///
/// let queue = MPSCQueue::<usize>::default();
///
/// queue.push(0x100);
/// queue.push(0x200);
///
/// let batch: Vec<usize> = queue.drain();
///
/// assert_eq!(batch.len(), 2);
/// assert_eq!(batch, vec![0x200, 0x100]);
/// ```
#[derive(Debug)]
pub struct MPSCQueue<T> {
    head: atomic::AtomicPtr<Node<T>>,
}

unsafe impl<T> Send for MPSCQueue<T> {}
unsafe impl<T> Sync for MPSCQueue<T> {}

impl<T> MPSCQueue<T> {
    /// Checks if the [`MPSCQueue`] is currently empty
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::mpscq::MPSCQueue;
    ///
    /// let queue = MPSCQueue::<usize>::default();
    /// assert!(queue.is_empty());
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.head.load(atomic::Ordering::Acquire).is_null()
    }

    /// Push an entry into the [`MPSCQueue`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::mpscq::MPSCQueue;
    ///
    /// let queue = MPSCQueue::<usize>::default();
    /// queue.push(0x0A);
    ///
    /// let batch = queue.drain();
    ///
    /// assert_eq!(batch.len(), 1);
    /// assert_eq!(batch, vec![0x0A]);
    /// ```
    #[inline(always)]
    pub fn push(&self, value: T) {
        let mut head = self.head.load(atomic::Ordering::Relaxed);
        let node = Node::new(value);

        loop {
            unsafe { (*node).next = head };
            match self.head.compare_exchange_weak(
                head,
                node,
                atomic::Ordering::AcqRel,
                atomic::Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(h) => head = h,
            }
        }
    }

    /// Drain the current batch of items from the [`MPSCQueue`]
    ///
    /// ## Ordering
    ///
    /// The queue internally uses a linked list like structure for storing `T`, therefore entries
    /// are stored in LIFO order.
    ///
    /// ## Multiple Consumers
    ///
    /// By design [`MPSCQueue::drain`] is thread safe, but draining from multiple threads is
    /// semantically incorrect. In the MPSC model, there should only be a single consumer, while
    /// there can be many producers.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::mpscq::MPSCQueue;
    ///
    /// let queue = MPSCQueue::<u8>::default();
    ///
    /// queue.push(0x0A);
    /// queue.push(0x0B);
    /// queue.push(0x0C);
    ///
    /// let batch = queue.drain();
    ///
    /// assert_eq!(batch.len(), 3);
    /// assert_eq!(batch, vec![0x0C, 0x0B, 0x0A]);
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
        Self { head: atomic::AtomicPtr::new(ptr::null_mut()) }
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
        Box::into_raw(Box::new(Self { next: ptr::null_mut(), value }))
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
