use core::ffi::CStr;
use core::slice;

use super::*;
use crate::error::{CStrLenError, InteriorNulError};
use NulByte::Nul;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(u8)]
enum NulByte {
    Nul = 0,
}

const fn count_bytes(val: &CStr) -> usize {
    // Avoid bumping the MSRV and stay `const` by using `unsafe`.
    let mut p = val.as_ptr();
    let mut other_len = 0;
    while unsafe { *p } != 0 {
        other_len += 1;
        p = unsafe { p.add(1) };
    }
    other_len
}

/// Fixed-size [`CStr`] stored as an array.
///
/// The length `N` is the number of bytes in the string _not_ including the nul terminator.
///
/// Because it has a fixed size, it can be put directly in a `static` and all
/// casting operations are constant-time.
// Note: As of writing, `&mut CStr` is not sound to construct.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(C)]
pub struct CStrArray<const N: usize> {
    // Always kept non-zero.
    data: [u8; N],
    nul: NulByte,
}

impl<const N: usize> CStrArray<N> {
    /// Builds a `CStrArray<N>` from a correct-length `val`.
    ///
    /// This performs a length validation.
    ///
    /// If `val` is a literal or `const`, consider using [`cstr_array!`]
    /// instead, which always builds a `CStrArray` with the correct `N`.
    pub const fn new(val: &CStr) -> Self {
        let other_len = count_bytes(val);
        if other_len != N {
            panic!("val.count_bytes() != N");
        }
        // SAFETY: `val` is checked to point to `N` non-nul bytes followed by a nul.
        unsafe { Self::new_unchecked(val) }
    }

    /// Fallibly builds a `StrArray<N>` from `val`.
    ///
    /// This returns an `Err` if `val.len() != N`.
    pub const fn new_checked(val: &CStr) -> Result<Self, CStrLenError<N>> {
        let other_len = count_bytes(val);
        if other_len != N {
            return Err(CStrLenError { other_len });
        }
        // SAFETY: `val` is checked to point to `N` non-nul bytes followed by a nul.
        Ok(unsafe { Self::new_unchecked(val) })
    }

    /// Builds a `StrArray<N>` from `val` without a size check.
    ///
    /// # Safety
    ///
    /// `val.count_bytes() == N`
    pub const unsafe fn new_unchecked(val: &CStr) -> Self {
        // SAFETY: `val` is known to point to `N` non-nul bytes followed by a nul.
        CStrArray {
            data: unsafe { *val.as_ptr().cast() },
            nul: Nul,
        }
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents.
    ///
    /// Note that this does _not_ include the nul terminator -
    /// it is appended automatically.
    pub const fn from_bytes_without_nul(bytes: &[u8; N]) -> Result<Self, InteriorNulError> {
        // Avoid bumping the MSRV and stay `const` by using a manual loop.
        let mut i = 0;
        while i + 1 < N {
            if bytes[i] == 0 {
                return Err(InteriorNulError { position: i });
            }
            i += 1;
        }
        Ok(Self {
            data: *bytes,
            nul: Nul,
        })
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents and no checks.
    ///
    /// Note that this does _not_ include the nul terminator -
    /// it is appended automatically.
    ///
    /// # Safety
    /// - `bytes` must not have any 0 (nul) bytes.
    pub const unsafe fn from_bytes_without_nul_unchecked(
        bytes: &[u8; N],
    ) -> Result<Self, InteriorNulError> {
        Ok(Self {
            data: *bytes,
            nul: Nul,
        })
    }

    /// Returns the fixed length.
    pub const fn len(&self) -> usize {
        N
    }

    /// Borrows this `CStrArray` as a `&CStr`.
    ///
    /// This is called by `Deref`.
    pub const fn as_c_str(&self) -> &CStr {
        // SAFETY:
        // - The first `N` bytes of `self` (`data` field) are kept non-nul.
        // - The last byte of `self` is always a nul byte.
        unsafe { CStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
    }

    /// Converts this C string to a byte array reference.
    ///
    /// The returned slice will not contain the trailing nul terminator
    /// that this C string has.
    pub const fn as_bytes(&self) -> &[u8; N] {
        &self.data
    }

    /// Converts this C string to a byte slice containing the trailing 0 byte.
    ///
    /// The length of the slice is `N + 1`.
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        // SAFETY:
        // - `Self` uses the `repr(C)` layout algorithm.
        // - The total size of `Self` is `N + 1`
        // - All bytes in `Self` are initialized.
        unsafe { slice::from_raw_parts(self as *const _ as *const u8, N + 1) }
    }

    /// Consumes `self` into its underlying array.
    pub const fn into_bytes(self) -> [u8; N] {
        self.data
    }

    /// Returns the fixed length.
    ///
    /// This uses the same name as [`CStr::count_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use len"]
    pub const fn count_bytes(&self) -> usize {
        self.len()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use as_bytes"]
    pub const fn to_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes_with_nul`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use as_bytes_with_nul"]
    pub const fn to_bytes_with_nul(&self) -> &[u8] {
        self.as_bytes_with_nul()
    }
}

impl Default for CStrArray<0> {
    fn default() -> Self {
        Self { data: [], nul: Nul }
    }
}

impl<const N: usize> Debug for CStrArray<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <CStr as Debug>::fmt(self.as_c_str(), f)
    }
}

impl<const N: usize> Deref for CStrArray<N> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

impl<const N: usize> AsRef<CStr> for CStrArray<N> {
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl<const N: usize> TryFrom<&CStr> for CStrArray<N> {
    type Error = CStrLenError<N>;

    fn try_from(val: &CStr) -> Result<Self, Self::Error> {
        Self::new_checked(val)
    }
}

#[cfg(feature = "alloc")]
mod alloc {
    use super::*;
    use ::alloc::ffi::CString;

    impl<const N: usize> TryFrom<Box<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Box<CStr>) -> Result<Self, Self::Error> {
            Self::new_checked(&val)
        }
    }

    impl<const N: usize> TryFrom<Rc<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Rc<CStr>) -> Result<Self, Self::Error> {
            Self::new_checked(&val)
        }
    }

    impl<const N: usize> TryFrom<Arc<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Arc<CStr>) -> Result<Self, Self::Error> {
            Self::new_checked(&val)
        }
    }

    impl<const N: usize> TryFrom<CString> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: CString) -> Result<Self, Self::Error> {
            Self::new_checked(&val)
        }
    }

    impl<const N: usize> PartialEq<CString> for CStrArray<N> {
        fn eq(&self, other: &CString) -> bool {
            self.as_c_str() == other.as_c_str()
        }
    }

    impl<const N: usize> PartialEq<CStrArray<N>> for CString {
        fn eq(&self, other: &CStrArray<N>) -> bool {
            self.as_c_str() == other.as_c_str()
        }
    }
}

impl<const N: usize> PartialEq<CStr> for CStrArray<N> {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str() == other
    }
}

impl<const N: usize> PartialEq<CStrArray<N>> for CStr {
    fn eq(&self, other: &CStrArray<N>) -> bool {
        self == other.as_c_str()
    }
}

impl<const N: usize> PartialEq<&CStr> for CStrArray<N> {
    fn eq(&self, other: &&CStr) -> bool {
        self.as_c_str() == *other
    }
}

impl<const N: usize> PartialEq<CStrArray<N>> for &CStr {
    fn eq(&self, other: &CStrArray<N>) -> bool {
        *self == other.as_c_str()
    }
}

/// Builds [`CStrArray`] from constant `&CStr`.
///
/// # Examples
///
/// Pass a `const` expression of `&CStr` to build a `CStrArray` with the same length.
///
/// ```
/// # use core::ffi::CStr;
/// # use str_array::cstr_array;
/// let x = cstr_array!(c"Buzz");
/// assert_eq!(x.len(), 4);
///
/// const NAME: &CStr = c"Sally";
/// let y = cstr_array!(NAME);
/// assert_eq!(y, c"Sally");
/// ```
///
/// Define `static` or `const` items, using `_` for the string length.
/// The length of the array uses the length of the assigned string.
/// Note that the assignment expression currently is evaluated twice,
/// but this should have no effect due to it being in `const`.
///
/// ```
/// # use core::ptr::addr_of;
/// # use str_array::{cstr_array, CStrArray};
/// cstr_array! {
///     static STATIC: CStrArray<_> = c"static";
///     static mut STATIC_MUT: CStrArray<_> = c"static_mut";
///     const CONST: CStrArray<_> = c"constant";
/// }
/// assert_eq!(STATIC, c"static");
/// assert_eq!(unsafe { &*addr_of!(STATIC_MUT) }, c"static_mut");
/// assert_eq!(CONST, c"constant");
/// ```
// TODO: Support plain string literals too (requires a nul check).
#[macro_export]
macro_rules! cstr_array {
    // TODO: same caveats as str_array
    (@impl item
        ($([$attr:meta])*)
        ($($item_kind:tt)*)
        $name:ident: $strarray_ty:ty = $val:expr; $($rest:tt)*
    ) => {
        $(#[$attr])* $($item_kind)* $name: $crate::CStrArray<{$val.count_bytes()}> = $crate::CStrArray::new($val);
        $crate::cstr_array!($($rest)*)
    };
    ($(#[$attr:meta])* static mut $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (static mut) $($rest)*);
    };
    ($(#[$attr:meta])* static $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (static) $($rest)*);
    };
    ($(#[$attr:meta])* const $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (const) $($rest)*);
    };
    ($val:expr) => {{
        const VAL: &::core::ffi::CStr = $val;
        const ARRAY: $crate::CStrArray<{ VAL.count_bytes() }> = $crate::CStrArray::new(VAL);
        ARRAY
    }};
    () => {};
}
