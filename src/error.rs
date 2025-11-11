use core::fmt::{self, Debug, Display};

#[cfg(all(has_core_error, not(feature = "std")))]
use core::error::Error;

#[cfg(all(not(has_core_error), feature = "std"))]
use std::error::Error;

/// Failed to construct `StrArray<N>` from a different-length `&str`.
pub struct StrLenError<const N: usize> {
    pub(crate) other_len: usize,
}

impl<const N: usize> Debug for StrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StrLenError<{N}> {{ other_len: {} }}", self.other_len)
    }
}
impl<const N: usize> Display for StrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Failed to construct `StrArray<N>` from `&str` with len {}",
            self.other_len
        )
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl<const N: usize> Error for StrLenError<N> {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn test_debug() {
        let err = StrLenError::<10> { other_len: 5 };
        assert_eq!(format!("{:?}", err), "StrLenError<10> { other_len: 5 }");
    }

    #[test]
    fn test_display() {
        let err = StrLenError::<10> { other_len: 5 };
        assert_eq!(
            format!("{}", err),
            "Failed to construct `StrArray<N>` from `&str` with len 5"
        );
    }
}
