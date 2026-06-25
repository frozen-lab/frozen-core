//! Benchmarks for `reservoir` module
//! Run using: `taskset -c 2,3,4 cargo bench --bench reservoir`

use frozen_core::reservoir::Reservoir;
use hdrhistogram::Histogram;
use std::{sync, thread, time};

const THREADS: usize = 4;
const OPS: usize = 0xF4240;
const WARMUP_OPS: usize = OPS >> 0x0A;
const OPS_PER_THREAD: usize = OPS / THREADS;
const CAPACITY: usize = 0x400;

fn init() -> Reservoir<usize> {
    let resources = vec![0; CAPACITY];
    Reservoir::new(resources)
}

fn print_results(hist: &Histogram<u64>) {
    println!();
    println!("| Metric     | Value (ns)    |");
    println!("|:-----------|:--------------|");
    println!("| P50        | {:.4}         |", hist.value_at_quantile(0.50) as f64);
    println!("| P90        | {:.4}         |", hist.value_at_quantile(0.90) as f64);
    println!("| P99        | {:.4}         |", hist.value_at_quantile(0.99) as f64);
    println!("| MEAN       | {:.4}         |", hist.mean() as f64);
    println!();
}

fn single_tx_acquire_latency() {
    println!("benching single thread acquire latency...");
    println!();
    println!("*NOTE:* Measured w/ {OPS} operations");
    println!("*NOTE:* Uncontended fast-path (lock-free)");
    println!();

    let pool = init();

    // warmup
    for _ in 0..WARMUP_OPS {
        let _permit = pool.acquire();
    }

    const BATCH_SIZE: usize = 0x64;
    let iterations = OPS / BATCH_SIZE;

    let mut hist = Histogram::<u64>::new(3).expect("new histogram");
    for _ in 0..iterations {
        let start = time::Instant::now();
        for _ in 0..BATCH_SIZE {
            let _permit = pool.acquire();
        }

        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let latency_per_op = elapsed_ns / (BATCH_SIZE as u64);
        hist.record(latency_per_op).expect("push measurement");
    }

    print_results(&hist);
}

fn multi_tx_acquire_latency() {
    println!("benching multi thread acquire latency...");
    println!();
    println!("*NOTE:* Measured w/ {OPS} total operations");
    println!("*NOTE:* {OPS_PER_THREAD} operations per thread w/ {THREADS} concurrent threads");
    println!("*NOTE:* High CAS contention path");
    println!();

    let pool = sync::Arc::new(init());
    let mut handles = Vec::with_capacity(THREADS);

    for _ in 0..THREADS {
        let pool = sync::Arc::clone(&pool);

        handles.push(thread::spawn(move || {
            // warmup
            for _ in 0..WARMUP_OPS {
                let _permit = pool.acquire();
            }

            let mut hist = Histogram::<u64>::new(3).expect("new histogram");
            for _ in 0..OPS_PER_THREAD {
                let start = time::Instant::now();
                let _permit = pool.acquire();

                let latency_ns = start.elapsed().as_nanos() as u64;
                hist.record(latency_ns).expect("push measurement");
            }

            hist
        }));
    }

    let mut hist = Histogram::<u64>::new(3).expect("new histogram");
    for handle in handles {
        let local_hist = handle.join().expect("worker should join");
        hist.add(&local_hist).expect("merge histogram");
    }

    print_results(&hist);
}

fn main() {
    single_tx_acquire_latency();
    println!("--------------------------------------------------");
    multi_tx_acquire_latency();
}
