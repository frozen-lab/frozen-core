//! Custom implementations for [`Result<T>`] and [`Err<T>`]

/// Custom result type w/ [`FrozenErr`] as error type
pub type FrozenRes<T> = Result<T, FrozenErr>;

/// Custom error object used in [`FrozenRes`]
#[derive(Clone, Eq, PartialEq)]
pub struct FrozenErr {
    module: u8,
    domain: u8,
    context: u16,
    message: alloc::vec::Vec<u8>,
}

impl FrozenErr {
    /// constrcut a new instance from raw id's
    #[inline]
    pub const fn new(module: u8, domain: u8, context: u16, message: alloc::vec::Vec<u8>) -> Self {
        Self {
            module,
            domain,
            context,
            message,
        }
    }

    /// compare [`Self::context`] w/ given `context` id
    #[inline]
    pub const fn cmp(&self, context: u16) -> bool {
        self.context == context
    }
}

impl core::fmt::Display for FrozenErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let msg = core::str::from_utf8(&self.message).unwrap_or("<non-utf8>");
        write!(f, "[m={}, d={}, c={}] {msg}", self.module, self.domain, self.context,)
    }
}

/// Default `module_id` for testing
#[cfg(test)]
pub const TEST_MID: u8 = 0x00;
