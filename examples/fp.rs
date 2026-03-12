use frozen_core::bpool::{BPBackend, BPCfg, BufPool};
use frozen_core::ffile::{FFCfg, FrozenFile};
use frozen_core::fpipe::FrozenPipe;
use std::time::Duration;

fn main() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("tmp_pipe");

    let file = FrozenFile::new(FFCfg {
        path,
        mid: 0,
        chunk_size: 0x20,
        initial_chunk_amount: 4,
    })
    .unwrap();

    let pool = BufPool::new(BPCfg {
        mid: 0,
        chunk_size: 0x20,
        backend: BPBackend::Prealloc { capacity: 0x10 },
    });

    let pipe = FrozenPipe::new(file, pool, Duration::from_micros(0x3A)).unwrap();

    let buf = vec![1u8; 0x40];
    let epoch = pipe.write(&buf, 0).unwrap();

    pipe.wait_for_durability(epoch).unwrap();

    let read = pipe.read(0, 2).unwrap();
    assert_eq!(read, buf);
}
