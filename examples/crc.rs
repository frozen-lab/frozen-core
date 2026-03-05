use frozen_core::crc::Crc32C;

fn main() {
    let crc = Crc32C::new();

    let b0: [u8; 8] = *b"12345678";
    let b1: [u8; 8] = *b"ABCDEFGH";
    let b2: [u8; 8] = *b"abcdefgh";
    let b3: [u8; 8] = *b"zyxwvuts";

    assert_eq!(crc.crc(&b0), crc.crc(&b0));
    assert_eq!(crc.crc_2x([&b0, &b1]), crc.crc_2x([&b0, &b1]));
    assert_eq!(crc.crc_4x([&b0, &b1, &b2, &b3]), crc.crc_4x([&b0, &b1, &b2, &b3]));
}
