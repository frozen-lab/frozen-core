use frozen_core::ff::{FFCfg, FrozenFile};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = FrozenFile::new(FFCfg::new(path, MODULE_ID), 16).expect("create");
    assert!(ff.fd() >= 0);
}
