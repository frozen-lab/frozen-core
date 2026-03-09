use frozen_core::mpscq::MPSCQueue;

fn main() {
    let queue = MPSCQueue::<usize>::default();

    queue.push(1usize);
    queue.push(2usize);
    queue.push(3usize);

    let batch = queue.drain();

    assert_eq!(batch.len(), 3);
    assert_eq!(batch, vec![3usize, 2usize, 1usize]);

    drop(batch); // values is dropped here
}
