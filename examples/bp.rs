// use frozen_core::bpool::BPool;
// use std::sync::Arc;
// use std::thread;

// const MODULE_ID: u8 = 0;
// const CAPACITY: usize = 8;
// const BUF_SIZE: usize = 0x20;

// fn main() {
//     let pool = Arc::new(BPool::new(BUF_SIZE, CAPACITY, MODULE_ID));

//     let mut handles = Vec::new();
//     for _ in 0..4 {
//         let pool = pool.clone();

//         handles.push(thread::spawn(move || {
//             for _ in 0..0x80 {
//                 let mut n = 2;
//                 while n != 0 {
//                     let alloc = pool.allocate(n);

//                     // pool when not all bufs are allocated
//                     if alloc.count == 0 {
//                         pool.wait().expect("wait failed");
//                         continue;
//                     }

//                     n -= alloc.count;
//                 }

//                 // NOTE: allocated bufs are freed automatically when `alloc` drops
//             }
//         }));
//     }

//     for h in handles {
//         h.join().unwrap();
//     }
// }

fn main() {}
