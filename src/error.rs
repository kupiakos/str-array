use super::*;

/// Failed to construct `StrArray<N>` from a different-length `&str`.
pub struct StrLenError<const N: usize> {
    pub other_len: usize,
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
            "Failed to construct `StrArray<{N}>` from `&str` with len {}",
            self.other_len
        )
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl<const N: usize> Error for StrLenError<N> {}

/// Failed to construct `CStrArray<N>` from a different-length `&CStr`.
pub struct CStrLenError<const N: usize> {
    pub other_len: usize,
}

impl<const N: usize> Debug for CStrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CStrLenError<{N}> {{ other_len: {} }}", self.other_len)
    }
}
impl<const N: usize> Display for CStrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Failed to construct `CStrArray<{N}>` from `&CStr` with len {}",
            self.other_len
        )
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl<const N: usize> Error for CStrLenError<N> {}

/// Data provided contains an interior nul byte at byte `position`.
#[derive(Debug)]
pub struct InteriorNulError {
    /// The position of the interior nul byte.
    pub position: usize,
}

impl Display for InteriorNulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Interior nul at byte {}", self.position)
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl Error for InteriorNulError {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn test_str_len_error_debug() {
        let err = StrLenError::<10> { other_len: 5 };
        assert_eq!(format!("{err:?}"), "StrLenError<10> { other_len: 5 }");
    }

    #[test]
    fn test_str_len_error_display() {
        let err = StrLenError::<10> { other_len: 5 };
        assert_eq!(
            format!("{err}"),
            "Failed to construct `StrArray<10>` from `&str` with len 5"
        );
    }

    #[test]
    fn test_c_str_len_debug() {
        let err = CStrLenError::<10> { other_len: 5 };
        assert_eq!(format!("{err:?}"), "CStrLenError<10> { other_len: 5 }");
    }

    #[test]
    fn test_c_str_len_display() {
        let err = CStrLenError::<10> { other_len: 5 };
        assert_eq!(
            format!("{err}"),
            "Failed to construct `CStrArray<10>` from `&CStr` with len 5"
        );
    }

    #[test]
    fn test_interior_nul_error_display() {
        let err = InteriorNulError { position: 10 };
        assert_eq!(format!("{err}"), "Interior nul at byte 10");
    }
}
