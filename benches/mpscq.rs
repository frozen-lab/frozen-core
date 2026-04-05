//! Benchmarks for `mpscq` module
//! Run using: `taskset -c 2,3,4 cargo bench --bench mpscq --features=mpscq`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use frozen_core::mpscq::MPSCQueue;
use std::hint::black_box;
use std::sync::Arc;

fn bench_mpscq(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpscq");

    // single tx push
    for &n in &[1, 8, 0x40, 0x100] {
        let q = MPSCQueue::default();
        group.bench_with_input(BenchmarkId::new("single_push", n), &n, |b, &n| {
            b.iter(|| {
                for i in 0..n {
                    q.push(black_box(i));
                }

                // cleanup
                let _ = q.drain();
            });
        });
    }

    // single tx drain
    for &n in &[1, 8, 0x40, 0x100] {
        group.bench_with_input(BenchmarkId::new("single_drain", n), &n, |b, &n| {
            b.iter(|| {
                let q = MPSCQueue::default();

                for i in 0..n {
                    q.push(i);
                }

                let batch = q.drain();
                black_box(batch);
            });
        });
    }

    // push + drain cycle
    for &n in &[1, 8, 0x40, 0x100] {
        let q = MPSCQueue::default();

        group.bench_with_input(BenchmarkId::new("cycle", n), &n, |b, &n| {
            b.iter(|| {
                for i in 0..n {
                    q.push(i);
                }

                let batch = q.drain();
                black_box(batch);
            });
        });
    }

    // benching multi-producer contention
    for &threads in &[2, 4, 8] {
        group.bench_with_input(BenchmarkId::new("contention_push", threads), &threads, |b, &threads| {
            let q = Arc::new(MPSCQueue::default());
            b.iter(|| {
                std::thread::scope(|s| {
                    for _ in 0..threads {
                        let q = q.clone();
                        s.spawn(move || {
                            for i in 0..0x40 {
                                q.push(black_box(i));
                            }
                        });
                    }
                });

                let batch = q.drain();
                black_box(batch);
            });
        });
    }

    // benching producer + consumer (multi tx)
    group.bench_function("produ_consume", |b| {
        let q = Arc::new(MPSCQueue::default());

        b.iter(|| {
            let producer = {
                let q = q.clone();
                std::thread::spawn(move || {
                    for i in 0..0x100 {
                        q.push(i);
                    }
                })
            };

            let consumer = {
                let q = q.clone();
                std::thread::spawn(move || {
                    let mut total = 0;
                    while total < 0x100 {
                        let batch = q.drain();
                        total += batch.len();
                    }
                })
            };

            producer.join().unwrap();
            consumer.join().unwrap();
        });
    });

    group.finish();
}

criterion_group!(benches, bench_mpscq);
criterion_main!(benches);
