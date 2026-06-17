//! Benchmarks for `wpipe` module
//! Run using: `taskset -c 2,3,4 cargo bench --bench wpipe --features=wpipe`

use frozen_core::{bufpool, ffile, utils, wpipe};
use hdrhistogram::Histogram;
use std::{ptr, sync, time};

const THREADS: usize = 4;
const MODULE_ID: u8 = 0x00;
const OPS: usize = 0x100_000;
const WARMUP_OPS: usize = OPS >> 0x0A;
const OPS_PER_THREAD: usize = OPS / THREADS;
const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
const PAYLOAD: [u8; BUFFER_SIZE as usize] = [0xAAu8; BUFFER_SIZE as usize];

fn init<P: AsRef<std::path::Path>>(
    path: P,
) -> (sync::Arc<ffile::FrozenFile>, bufpool::BufPool, wpipe::WritePipe) {
    let file_cfg = ffile::FFCfg {
        path: path.as_ref().to_path_buf(),
        chunk_size: BUFFER_SIZE as usize,
        initial_chunk_amount: OPS,
    };
    let file = sync::Arc::new(ffile::FrozenFile::new::<MODULE_ID>(file_cfg).expect("new ffile"));

    let pool_cfg =
        bufpool::BufPoolCfg { buffer_size: BUFFER_SIZE, max_memory: OPS * BUFFER_SIZE as usize };
    let pool = bufpool::BufPool::new(pool_cfg);

    let pipe_cfg = wpipe::WritePipeCfg {
        module_id: MODULE_ID,
        flush_duration: time::Duration::from_millis(1),
    };
    let pipe = wpipe::WritePipe::new(pipe_cfg, file.clone()).expect("new wpipe");

    (file, pool, pipe)
}

fn record_bench(pipe: &wpipe::WritePipe, pool: &bufpool::BufPool) -> Histogram<u64> {
    let mut hist = Histogram::<u64>::new(3).expect("new histogram");
    for i in 0..OPS {
        let allocation = pool.allocate(1);
        unsafe {
            ptr::copy_nonoverlapping(PAYLOAD.as_ptr(), allocation.first(), BUFFER_SIZE as usize)
        };

        let req = wpipe::WriteRequest { allocation, slot_index: i };
        let start = time::Instant::now();

        let _ticket = pipe.write(req).expect("push write");
        let latency_ns = start.elapsed().as_nanos() as u64;

        hist.record(latency_ns).expect("push measurement");
    }

    hist
}

fn print_results(hist: &Histogram<u64>) {
    println!();
    println!("| Metric     | Value (µs)    |");
    println!("|:-----------|:--------------|");
    println!("| P50        | {:.4}         |", hist.value_at_quantile(0.50) as f64 / 1000.0);
    println!("| P90        | {:.4}         |", hist.value_at_quantile(0.90) as f64 / 1000.0);
    println!("| P99        | {:.4}         |", hist.value_at_quantile(0.99) as f64 / 1000.0);
    println!("| MEAN       | {:.4}         |", hist.mean() as f64 / 1000.0);
    println!();
}

fn single_tx_write_latency() {
    println!("benching single thread write latency...");

    println!();
    println!("*NOTE:* Measured w/ {OPS} operations");
    println!();

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("wpipe_bench_latency");
    let (_file, pool, pipe) = init(path);

    // warmup
    for i in 0..WARMUP_OPS {
        let allocation = pool.allocate(1);
        unsafe {
            ptr::copy_nonoverlapping(PAYLOAD.as_ptr(), allocation.first(), BUFFER_SIZE as usize)
        };

        let req = wpipe::WriteRequest { allocation, slot_index: i };
        let _ticket = pipe.write(req).expect("push write");
    }

    let hist = record_bench(&pipe, &pool);
    print_results(&hist);
}

fn multi_tx_write_latency() {
    println!("benching multi thread write latency...");

    println!();
    println!("*NOTE:* Measured w/ {OPS} total operations");
    println!("*NOTE:* {OPS_PER_THREAD} operations per thread w/ {THREADS} concurrent threads");
    println!();

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("wpipe_bench_latency");
    let (_file, pool, pipe) = init(path);

    let pipe = sync::Arc::new(pipe);
    let pool = sync::Arc::new(pool);

    let mut handles = Vec::with_capacity(THREADS);
    for tid in 0..THREADS {
        let pipe = sync::Arc::clone(&pipe);
        let pool = sync::Arc::clone(&pool);

        handles.push(std::thread::spawn(move || {
            // warmup
            for i in 0..WARMUP_OPS {
                let allocation = pool.allocate(1);
                unsafe {
                    ptr::copy_nonoverlapping(
                        PAYLOAD.as_ptr(),
                        allocation.first(),
                        BUFFER_SIZE as usize,
                    )
                };

                let req = wpipe::WriteRequest { allocation, slot_index: i };
                let _ticket = pipe.write(req).expect("push write");
            }

            let mut hist = Histogram::<u64>::new(3).expect("new histogram");
            for i in 0..OPS_PER_THREAD {
                let allocation = pool.allocate(1);
                unsafe {
                    ptr::copy_nonoverlapping(
                        PAYLOAD.as_ptr(),
                        allocation.first(),
                        BUFFER_SIZE as usize,
                    )
                };

                let req = wpipe::WriteRequest { allocation, slot_index: tid * OPS_PER_THREAD + i };
                let start = time::Instant::now();

                let _ticket = pipe.write(req).expect("push write");
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
    single_tx_write_latency();
    multi_tx_write_latency();
}
