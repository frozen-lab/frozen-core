use core::{ptr, sync::atomic};

#[derive(Debug)]
pub struct MPSCQueue<T> {
    head: atomic::AtomicPtr<Node<T>>,
}

impl<T> MPSCQueue<T> {
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
