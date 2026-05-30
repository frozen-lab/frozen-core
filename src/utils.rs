//! Common utilities used in [`frozen_core`]

/// Returns `true` if `x` is a power of two.
///
/// ## Example
///
/// ```
/// use frozen_core::utils::is_power_of_2;
///
/// assert!(is_power_of_2(1u16));
/// assert!(is_power_of_2(2u32));
/// assert!(is_power_of_2(4u64));
/// assert!(is_power_of_2(1024usize));
///
/// assert!(!is_power_of_2(0u16));
/// assert!(!is_power_of_2(3u32));
/// assert!(!is_power_of_2(5u64));
/// assert!(!is_power_of_2(1023usize));
/// ```
#[inline]
pub fn is_power_of_2<T>(x: T) -> bool
where
    T: Copy + Eq + From<u8> + core::ops::Sub<Output = T> + core::ops::BitAnd<Output = T>,
{
    let zero = T::from(0);
    x != zero && (x & (x - T::from(1))) == zero
}

/// Size of a single IO buffer.
///
/// All variants are powers of two, which enables efficient alignment, masking, indexing, and allocator-friendly
/// memory layouts throughout the storage engine.
///
/// The value of each variant is the buffer size in bytes.
///
/// ## Example
///
/// ```
/// let buf_size = frozen_core::utils::BufferSize::S128.bytes();
/// assert!(frozen_core::utils::is_power_of_2(buf_size));
/// ```
#[repr(usize)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BufferSize {
    /// 8 bytes
    S8 = 0x08,

    /// 16 bytes
    S16 = 0x10,

    /// 32 bytes
    S32 = 0x20,

    /// 64 bytes
    S64 = 0x40,

    /// 128 bytes
    S128 = 0x80,

    /// 256 bytes
    S256 = 0x100,

    /// 512 bytes
    S512 = 0x200,

    /// 1 KiB (1024 bytes)
    S1024 = 0x400,

    /// 2 KiB (2048 bytes)
    S2048 = 0x800,

    /// 4 KiB (4096 bytes)
    S4096 = 0x1000,
}

impl BufferSize {
    /// Returns the buffer size in bytes
    #[inline]
    pub const fn bytes(self) -> usize {
        self as usize
    }
}
