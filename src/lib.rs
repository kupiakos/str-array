//! Provides fixed-size string types [`StrArray<N>`] and [`CStrArray<N>`].
//!
//! [`StrArray`] serves as the `str` equivalent of `[u8; N]`, offering a `Deref`
//! to `&str` and ensuring the UTF-8 invariant is always upheld, but with a
//! size known at compile time. This is designed for `no_std` environments
//! or where strings are always a certain size.
//!
//! The [`str_array!`] macro provides a compile-time-checked way to
//! build [`StrArray`] values from string literals and constants.
//!
//! Similarly, [`CStrArray`] and [`cstr_array!`] can construct a nul-terminated
//! C string safely on the stack.
//!
//! # Features
//!
//! - `no_std` support - disable default features to use
//! - Optional `alloc` and `std` features
//! - `const` support
//! - [C string](CStrArray) support
//! - Full test coverage
//!
//! # Examples
//!
//! ```
//! use str_array::{str_array, StrArray};
//!
//! // Create from a literal using the macro. The length is inferred.
//! let s1 = str_array!("hello");
//! assert_eq!(s1.len(), 5);
//! assert_eq!(s1, "hello");
//!
//! // Or create from a &str with an panicking length check.
//! let s2: StrArray<12> = StrArray::new(&format!("{s1}, world"));
//! assert_eq!(core::mem::size_of_val(&s2), 12);
//! assert_eq!(s2, "hello, world");
//!
//! // Or create from bytes with a UTF-8 check.
//! let s3 = StrArray::from_utf8(
//!     b"\xF0\x9F\xA4\x8C\xF0\x9F\x8F\xBC"
//! ).unwrap();
//! assert_eq!(s3, "🤌🏼");
//!
//! // Or define an item with an inferred length.
//! str_array! {
//!     static S4: StrArray<_> = "Georgia";
//! }
//! assert_eq!(S4.len(), 7);
//! ```
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
use alloc::{
    borrow::{Borrow, BorrowMut},
    boxed::Box,
    rc::Rc,
    string::String,
    sync::Arc,
};
use core::{
    fmt::{self, Debug, Display},
    ops::{Deref, DerefMut},
    str::{FromStr, Utf8Error},
};

#[cfg(all(has_core_error, not(feature = "std")))]
use core::error::Error;

#[cfg(all(not(has_core_error), feature = "std"))]
use std::error::Error;

mod cmp;
mod convert;
mod cstr;
pub mod error;

pub use cstr::CStrArray;
use error::StrLenError;

/// Fixed-size [`str`] stored as a [`[u8; N]`][core::array].
///
/// `[u8; N]` is to `[u8]` as `StrArray<N>` is to `str`.
/// `StrArray<N>` is a `[u8; N]` which upholds the same UTF-8
/// invariant as `str`. It `Deref`s to `str` and
/// can be accessed as a `[u8; N]`.
///
/// [`str_array!`] provides a convenient way to construct
/// and define `StrArray` from literals and constants.
///
/// # Examples
///
/// Small strings that still must be UTF-8:
/// ```
/// # use str_array::{StrArray, str_array};
/// type AirportCode = StrArray<3>;
/// let mut airports = [
///     "JFK", "LAX", "LHR", "CDG", "HND",
///     "PEK", "DXB", "AMS", "FRA", "SIN",
/// ].map(AirportCode::new);
///
/// // All of the strings are contiguous in memory.
/// assert_eq!(core::mem::size_of_val(&airports), 30);
///
/// airports.sort();
/// assert_eq!(airports[0], "AMS");
/// ```
///
/// Storing `str` contents directly in a `static`:
///
/// ```
/// # use core::mem::size_of_val;
/// # use str_array::{StrArray, str_array};
/// str_array! {
///     static FOO: StrArray<_> = include_str!("foo.txt");
///     static mut FOO_MUT: StrArray<_> = "utf-8 buffer";
/// }
/// assert_eq!(&FOO, "Hello, world!");
/// assert_eq!(size_of_val(&FOO), 13);
/// let foo_mut = unsafe { &mut *&raw mut FOO_MUT };
/// foo_mut.make_ascii_uppercase();
/// assert_eq!(foo_mut, "UTF-8 BUFFER");
/// assert_eq!(size_of_val(foo_mut), 12);
/// ```
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct StrArray<const N: usize>(
    /// # Safety
    /// Must be UTF-8 encoded bytes.
    [u8; N],
);

impl<const N: usize> Default for StrArray<N> {
    fn default() -> Self {
        Self::zeroed()
    }
}

impl<const N: usize> Debug for StrArray<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StrArray<{N}>({s:?})", s = self.as_str())
    }
}

impl<const N: usize> Display for StrArray<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as Display>::fmt(self.as_str(), f)
    }
}

/// Wraps a _single function_ to be a `const` mut fn.
///
/// The `build.rs` checks if `&mut` works in `const` to enable `cfg(has_const_mut)`.
#[cfg(has_const_mut)]
macro_rules! const_mut_fn {
    ($(#[$m:meta])* $vis:vis unsafe fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis const unsafe fn $($rest)*
    };
    ($(#[$m:meta])* $vis:vis fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis const fn $($rest)*
    };
}

/// The `build.rs` checks if `&mut` works in `const` to enable `cfg(has_const_mut)`.
#[cfg(not(has_const_mut))]
macro_rules! const_mut_fn {
    ($(#[$m:meta])* $vis:vis unsafe fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis unsafe fn $($rest)*
    };
    ($(#[$m:meta])* $vis:vis fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis fn $($rest)*
    };
}

impl<const N: usize> StrArray<N> {
    /// Builds a `StrArray<N>` from a correct-length `val`.
    ///
    /// If `val` is a literal or `const`, consider using [`str_array!`]
    /// instead, which always builds a `StrArray` with the correct `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s: StrArray<5> = StrArray::new("hello");
    /// assert_eq!(s, "hello");
    /// ```
    ///
    /// The size of the `StrArray` must exactly match the input size:
    ///
    /// ```should_panic
    /// # use str_array::StrArray;
    /// _ = StrArray::<3>::new("hello");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `val.len() != N`.
    #[track_caller]
    pub const fn new(val: &str) -> Self {
        if val.len() == N {
            // SAFETY: `val.len() == N` as required.
            unsafe { Self::new_unchecked(val) }
        } else {
            panic!("val.len() != N")
        }
    }

    /// Fallibly builds a `StrArray<N>` from `val`.
    ///
    /// This returns an `Err` if `val.len() != N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::new_checked("hello").unwrap();
    /// assert_eq!(s, "hello");
    /// assert!(StrArray::<5>::new_checked("foo").is_err());
    /// ```
    pub const fn new_checked(val: &str) -> Result<Self, StrLenError<N>> {
        if val.len() == N {
            Ok(Self::new(val))
        } else {
            Err(StrLenError {
                other_len: val.len(),
            })
        }
    }

    /// Builds a `StrArray<N>` from `val` without a size check.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// // SAFETY: "hello" has length 5
    /// let s = unsafe { StrArray::<5>::new_unchecked("hello") };
    /// assert_eq!(s, "hello");
    /// ```
    ///
    /// # Safety
    ///
    /// `val.len() >= N`
    pub const unsafe fn new_unchecked(val: &str) -> Self {
        // SAFETY: `val` has at least size `N` as promised by the caller.
        Self(unsafe { *(val.as_bytes() as *const [u8]).cast() })
    }

    /// Converts a `&str` to `&StrArray<N>` without copying.
    ///
    /// This returns an `Err` if `val.len() != N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::ref_from_str("hello").unwrap();
    /// assert_eq!(s, "hello");
    ///
    /// assert!(StrArray::<5>::ref_from_str("foo").is_err());
    /// ```
    pub const fn ref_from_str(val: &str) -> Result<&Self, StrLenError<N>> {
        if val.len() != N {
            return Err(StrLenError {
                other_len: val.len(),
            });
        }
        // SAFETY:
        // - `StrArray<N>` is `repr(transparent)` over `[u8; N]`, as is `str`.
        // - We've checked that `*val` has the same size as `[u8; N]`.
        // - `str` is UTF-8, matching the requirement of Self::0.
        // - `val` is valid UTF-8.
        Ok(unsafe { &*val.as_ptr().cast() })
    }

    const_mut_fn! {
        /// Converts a `&mut str` to `&mut StrArray<N>` without copying.
        ///
        /// This returns an `Err` if `val.len() != N`.
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::StrArray;
        /// let mut s = String::from("hello");
        /// let s_mut = StrArray::<5>::mut_from_str(&mut s).unwrap();
        /// s_mut.make_ascii_uppercase();
        /// assert_eq!(s, "HELLO");
        ///
        /// assert!(StrArray::<5>::mut_from_str(&mut String::from("foo")).is_err());
        /// ```
        pub fn mut_from_str(val: &mut str) -> Result<&mut Self, StrLenError<N>> {
            if val.len() != N {
                return Err(StrLenError {
                    other_len: val.len(),
                });
            }
            // SAFETY:
            // - `StrArray<N>` is `repr(transparent)` over `[u8; N]`, as is `str`.
            // - We've checked that `*val` has the same size as `[u8; N]`.
            // - `val` is valid UTF-8.
            Ok(unsafe { &mut *val.as_mut_ptr().cast() })
        }
    }

    /// Copies UTF-8 bytes from `val` into a `StrArray<N>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::from_utf8(b"hello").unwrap();
    /// assert_eq!(s, "hello");
    /// ```
    pub const fn from_utf8(val: &[u8; N]) -> Result<Self, Utf8Error> {
        match Self::ref_from_utf8(val) {
            Ok(&a) => Ok(a),
            Err(e) => Err(e),
        }
    }

    /// Converts UTF-8 bytes in `val` to `&StrArray<N>` without copying.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::ref_from_utf8(b"hello").unwrap();
    /// assert_eq!(s, "hello");
    /// ```
    pub const fn ref_from_utf8(val: &[u8; N]) -> Result<&Self, Utf8Error> {
        match core::str::from_utf8(val) {
            // SAFETY:
            // - `StrArray<N>` is `repr(transparent)` over `[u8; N]`
            // - `val` is valid UTF-8
            Ok(_) => Ok(unsafe { &*(val as *const [u8; N]).cast() }),
            Err(e) => Err(e),
        }
    }

    const_mut_fn! {
        /// Converts UTF-8 bytes in `val` to `&mut StrArray<N>` without copying.
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::StrArray;
        /// let mut bytes = *b"hello";
        /// let s = StrArray::<5>::mut_from_utf8(&mut bytes).unwrap();
        /// assert_eq!(s, "hello");
        /// ```
        pub fn mut_from_utf8(val: &mut [u8; N]) -> Result<&mut Self, Utf8Error> {
            match core::str::from_utf8(val) {
                // SAFETY:
                // - `StrArray<N>` is `repr(transparent)` over `[u8; N]`
                // - `val` is valid UTF-8
                Ok(_) => Ok(unsafe { &mut *(val as *mut [u8; N]).cast() }),
                Err(e) => Err(e),
            }
        }
    }

    /// Returns a `StrArray<N>` filled with zeroes.
    ///
    /// This is also what [`Default::default`] returns for `Self`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<0>::zeroed();
    /// assert_eq!(s, "");
    /// ```
    pub const fn zeroed() -> Self {
        Self([0; N])
    }

    /// Borrows this `StrArray<N>` as a `&str`.
    ///
    /// This is performed automatically on deref.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::new("hello");
    /// assert_eq!(s.as_str().find('l'), Some(2));
    /// ```
    pub const fn as_str(&self) -> &str {
        // SAFETY: `self.0` is guaranteed to be UTF-8 bytes.
        unsafe { core::str::from_utf8_unchecked(&self.0) }
    }

    const_mut_fn! {
        /// Converts `&mut self` to a `&mut str`.
        ///
        /// This is performed automatically on deref.
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::StrArray;
        /// let mut s = StrArray::<5>::new("hello");
        /// s.as_mut_str().make_ascii_uppercase();
        /// assert_eq!(s, "HELLO");
        /// ```
        pub fn as_mut_str(&mut self) -> &mut str {
            // SAFETY: `self.0` is guaranteed to be UTF-8 bytes.
            unsafe { core::str::from_utf8_unchecked_mut(&mut self.0) }
        }
    }

    /// Borrows `self` as a byte array of the same size.
    ///
    /// Unlike [`str::as_bytes`], this returns an array reference.
    ///
    /// # Example
    ///
    /// ```
    /// # use str_array::{str_array, StrArray};
    /// let x = str_array!("Hello");
    /// let &[a, b @ .., c] = x.as_bytes();
    /// assert_eq!(a, b'H');
    /// assert_eq!(b, *b"ell");
    /// assert_eq!(c, b'o');
    /// ```
    pub const fn as_bytes(&self) -> &[u8; N] {
        &self.0
    }

    const_mut_fn! {
        /// Borrows `self` as a mutable byte array of the same size.
        ///
        /// Unlike [`str::as_bytes_mut`], this returns an array reference.
        ///
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::StrArray;
        /// let mut s = StrArray::<5>::new("hello");
        /// unsafe {
        ///    let bytes = s.as_mut_bytes();
        ///    bytes[0] = b'H';
        /// }
        /// assert_eq!(s, "Hello");
        /// ```
        /// # Safety
        /// This has the same non-local requirement as [`str::as_bytes_mut`]:
        ///
        /// The caller must ensure that the content of the array is valid UTF-8
        /// before the borrow ends and the underlying `StrArray` is used.
        pub unsafe fn as_mut_bytes(&mut self) -> &mut [u8; N] {
            &mut self.0
        }
    }

    /// Converts a `StrArray<N>` into a byte array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::{str_array, StrArray};
    /// let x = str_array!("Fizzy");
    ///
    /// let [a, b @ .., c] = x.into_bytes();
    /// assert_eq!(a, b'F');
    /// assert_eq!(b, *b"izz");
    /// assert_eq!(c, b'y');
    /// ```
    pub const fn into_bytes(self) -> [u8; N] {
        self.0
    }

    /// Returns the number of bytes in the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<5>::new("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    pub const fn len(&self) -> usize {
        N
    }
}

impl StrArray<0> {
    /// Returns an empty `StrArray`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::StrArray;
    /// let s = StrArray::<0>::empty();
    /// assert!(s.is_empty());
    /// ```
    pub const fn empty() -> Self {
        Self([])
    }
}

impl<const N: usize> Deref for StrArray<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> DerefMut for StrArray<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

/// Builds [`StrArray`] from constant `&str`.
///
/// # Examples
///
/// Pass a `const` expression of `&str` to build a `StrArray` with the same length.
///
/// ```
/// # use str_array::str_array;
/// let x = str_array!("Buzz");
/// assert_eq!(x.len(), 4);
///
/// const NAME: &str = "Sally";
/// let y = str_array!(NAME);
/// assert_eq!(y, "Sally");
/// ```
///
/// Define `static` or `const` items, using `_` for the string length.
/// The length of the array uses the length of the assigned string.
/// Note that the assignment expression currently is evaluated twice,
/// but this should have no effect due to it being in `const`.
///
/// ```
/// # use core::ptr::addr_of;
/// # use str_array::{StrArray, str_array};
/// str_array! {
///     static STATIC: StrArray<_> = "static";
///     static mut STATIC_MUT: StrArray<_> = "static_mut";
///     const CONST: StrArray<_> = "constant";
/// }
/// assert_eq!(STATIC, "static");
/// assert_eq!(unsafe { &*addr_of!(STATIC_MUT) }, "static_mut");
/// assert_eq!(CONST, "constant");
/// ```
#[macro_export]
macro_rules! str_array {
    // TODO: find a way to avoid the double-evaluation of `$val` for item declarations without adding a dependency.
    // TODO: support an explicit size instead of an underscore always
    // TODO: find a way to validate the type is what was mentioned and still allow the `_`.
    // ^ I'll probably need a proc macro for these
    (@impl item
        ($([$attr:meta])*)
        ($($item_kind:tt)*)
        $name:ident: $strarray_ty:ty = $val:expr; $($rest:tt)*
    ) => {
        $(#[$attr])* $($item_kind)* $name: $crate::StrArray<{$val.len()}> = $crate::StrArray::new($val);
        $crate::str_array!($($rest)*)
    };
    ($(#[$attr:meta])* static mut $($rest:tt)*) => {
        $crate::str_array!(@impl item ($([$attr])*) (static mut) $($rest)*);
    };
    ($(#[$attr:meta])* static $($rest:tt)*) => {
        $crate::str_array!(@impl item ($([$attr])*) (static) $($rest)*);
    };
    ($(#[$attr:meta])* const $($rest:tt)*) => {
        $crate::str_array!(@impl item ($([$attr])*) (const) $($rest)*);
    };
    ($val:expr) => {{
        const VAL: &str = $val;
        const ARRAY: $crate::StrArray<{ VAL.len() }> = $crate::StrArray::new(VAL);
        ARRAY
    }};
    () => {};
}

#[cfg(test)]
mod tests {
    use super::*;

    trait TypeEq {
        type This;
    }

    impl<T> TypeEq for T {
        type This = Self;
    }

    fn assert_type_eq_all<T, U>(_: U)
    where
        T: TypeEq<This = U>,
        U:,
    {
    }

    #[test]
    fn test_deref_mut() {
        let mut a = str_array!("aoeu");
        a.make_ascii_uppercase();
        assert_eq!(a, "AOEU");
    }

    #[test]
    #[cfg(has_const_mut)]
    fn test_const_mut() {
        const X: StrArray<3> = {
            let mut x = str_array!("foo");
            x.as_mut_str().make_ascii_uppercase();
            x
        };
        assert_eq!(X, "FOO");
    }

    // TODO: test using type alias for strarray and explicit len

    #[test]
    #[deny(non_upper_case_globals)]
    fn test_macro_declared_items() {
        // TODO: test attributes
        str_array! {
            /// With multi-line doc string
            ///
            /// and path from crate root.
            static STATIC: crate::StrArray<_> = "hello";

            #[allow(non_upper_case_globals)]
            static mut StaticMut: StrArray<_> = "aoeu";

            // With
            const CONST: StrArray<_> = "constant";
        }
        assert_eq!(STATIC, "hello");
        assert_type_eq_all::<StrArray<5>, _>(STATIC);
        assert_eq!(unsafe { StaticMut }, "aoeu");
        assert_type_eq_all::<StrArray<4>, _>(unsafe { StaticMut });

        let x = unsafe { &mut *core::ptr::addr_of_mut!(StaticMut) };
        x.make_ascii_uppercase();
        assert_eq!(x, "AOEU");

        assert_eq!(CONST, "constant");
        assert_type_eq_all::<StrArray<8>, _>(CONST);
    }

    #[test]
    fn test_slice() {
        let a = str_array!("a");
        let _: &str = &a[..];
    }
}
