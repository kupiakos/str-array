use crate::{error::StrLenError, StrArray};
use core::str::{FromStr, Utf8Error};

impl<const N: usize> FromStr for StrArray<N> {
    type Err = StrLenError<N>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl<const N: usize> TryFrom<&str> for StrArray<N> {
    type Error = StrLenError<N>;

    fn try_from(val: &str) -> Result<Self, Self::Error> {
        Self::new(val)
    }
}

impl<const N: usize> TryFrom<[u8; N]> for StrArray<N> {
    type Error = Utf8Error;

    fn try_from(val: [u8; N]) -> Result<Self, Self::Error> {
        Self::from_utf8(&val)
    }
}

impl<const N: usize> TryFrom<&[u8; N]> for StrArray<N> {
    type Error = Utf8Error;

    fn try_from(val: &[u8; N]) -> Result<Self, Self::Error> {
        Self::from_utf8(val)
    }
}

impl<'a, const N: usize> TryFrom<&'a [u8; N]> for &'a StrArray<N> {
    type Error = Utf8Error;

    fn try_from(val: &'a [u8; N]) -> Result<Self, Self::Error> {
        StrArray::ref_from_utf8(val)
    }
}

impl<'a, const N: usize> TryFrom<&'a mut [u8; N]> for &'a mut StrArray<N> {
    type Error = Utf8Error;

    fn try_from(val: &'a mut [u8; N]) -> Result<Self, Self::Error> {
        StrArray::mut_from_utf8(val)
    }
}

impl<'a, const N: usize> TryFrom<&'a str> for &'a StrArray<N> {
    type Error = StrLenError<N>;

    fn try_from(val: &'a str) -> Result<Self, Self::Error> {
        StrArray::ref_from_str(val)
    }
}

impl<'a, const N: usize> TryFrom<&'a mut str> for &'a mut StrArray<N> {
    type Error = StrLenError<N>;

    fn try_from(val: &'a mut str) -> Result<Self, Self::Error> {
        StrArray::mut_from_str(val)
    }
}

impl<'a, const N: usize> From<&'a StrArray<N>> for &'a str {
    fn from(val: &'a StrArray<N>) -> Self {
        val
    }
}

impl<'a, const N: usize> From<&'a mut StrArray<N>> for &'a mut str {
    fn from(val: &'a mut StrArray<N>) -> Self {
        val
    }
}

impl<'a, const N: usize> From<&'a StrArray<N>> for &'a [u8; N] {
    fn from(val: &'a StrArray<N>) -> Self {
        val.as_bytes()
    }
}

impl<'a, const N: usize> From<&'a StrArray<N>> for &'a [u8] {
    fn from(val: &'a StrArray<N>) -> Self {
        val.as_bytes()
    }
}

impl<const N: usize> From<StrArray<N>> for [u8; N] {
    fn from(s: StrArray<N>) -> Self {
        s.into_bytes()
    }
}

impl<const N: usize> AsRef<str> for StrArray<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsRef<[u8; N]> for StrArray<N> {
    fn as_ref(&self) -> &[u8; N] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<[u8]> for StrArray<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsMut<str> for StrArray<N> {
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

#[cfg(feature = "alloc")]
mod alloc {
    use crate::{error::StrLenError, StrArray};
    use ::alloc::{boxed::Box, rc::Rc, string::String, sync::Arc};
    use core::borrow::{Borrow, BorrowMut};

    impl<const N: usize> Borrow<str> for StrArray<N> {
        fn borrow(&self) -> &str {
            self.as_str()
        }
    }

    impl<const N: usize> BorrowMut<str> for StrArray<N> {
        fn borrow_mut(&mut self) -> &mut str {
            self.as_mut_str()
        }
    }

    impl<const N: usize> TryFrom<String> for StrArray<N> {
        type Error = StrLenError<N>;

        fn try_from(val: String) -> Result<Self, Self::Error> {
            Self::try_from(val.as_str())
        }
    }

    impl<const N: usize> TryFrom<Box<str>> for StrArray<N> {
        type Error = StrLenError<N>;

        fn try_from(val: Box<str>) -> Result<Self, Self::Error> {
            Self::try_from(val.as_ref())
        }
    }

    impl<const N: usize> TryFrom<Rc<str>> for StrArray<N> {
        type Error = StrLenError<N>;

        fn try_from(val: Rc<str>) -> Result<Self, Self::Error> {
            Self::try_from(val.as_ref())
        }
    }

    impl<const N: usize> TryFrom<Arc<str>> for StrArray<N> {
        type Error = StrLenError<N>;

        fn try_from(val: Arc<str>) -> Result<Self, Self::Error> {
            Self::try_from(val.as_ref())
        }
    }

    impl<const N: usize> From<StrArray<N>> for String {
        fn from(s: StrArray<N>) -> Self {
            s.as_str().into()
        }
    }

    impl<const N: usize> From<StrArray<N>> for Box<str> {
        fn from(s: StrArray<N>) -> Self {
            Box::from(s.as_str())
        }
    }

    impl<const N: usize> From<StrArray<N>> for Rc<str> {
        fn from(s: StrArray<N>) -> Self {
            Rc::from(s.as_str())
        }
    }

    impl<const N: usize> From<StrArray<N>> for Arc<str> {
        fn from(s: StrArray<N>) -> Self {
            Arc::from(s.as_str())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::str_array;

    use core::borrow::{Borrow, BorrowMut};

    #[test]
    fn test_borrow() {
        let s = str_array!("hello");
        let borrowed: &str = s.borrow();
        assert_eq!(borrowed, "hello");
    }

    #[test]
    fn test_borrow_mut() {
        let mut s = str_array!("hello");
        let borrowed: &mut str = s.borrow_mut();
        borrowed.make_ascii_uppercase();
        assert_eq!(borrowed, "HELLO");
    }

    #[test]
    fn test_from_str() {
        let s: StrArray<5> = "hello".parse().unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_try_from_str() {
        let s: StrArray<5> = "hello".try_into().unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_try_from_str_err() {
        let s: Result<StrArray<3>, _> = "hello".try_into();
        assert!(s.is_err());
    }

    #[test]
    fn test_try_from_bytes() {
        let s: StrArray<5> = StrArray::try_from(*b"hello").unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_try_from_bytes_slice() {
        let s: StrArray<5> = b"hello".try_into().unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_into_bytes() {
        let s: StrArray<5> = "hello".try_into().unwrap();
        let bytes: [u8; 5] = s.into();
        assert_eq!(&bytes, b"hello");
    }

    #[test]
    fn test_as_ref_str() {
        let s: StrArray<5> = "hello".try_into().unwrap();
        let r: &str = s.as_ref();
        assert_eq!(r, "hello");
    }

    #[test]
    fn test_as_ref_bytes() {
        let s: StrArray<5> = "hello".try_into().unwrap();
        let r: &[u8; 5] = s.as_ref();
        assert_eq!(r, b"hello");
    }

    #[test]
    fn test_as_ref_byte_slice() {
        let s: StrArray<5> = "hello".try_into().unwrap();
        let r: &[u8] = s.as_ref();
        assert_eq!(r, b"hello");
    }

    #[test]
    fn test_as_mut_str() {
        let mut s: StrArray<5> = "hello".try_into().unwrap();
        let mut_s: &mut str = s.as_mut();
        mut_s.make_ascii_uppercase();
        assert_eq!(mut_s, "HELLO");
    }

    #[test]
    fn test_try_from_mut_str() {
        let mut s = *b"hello";
        let s = str::from_utf8_mut(&mut s).unwrap();
        let sa: &mut StrArray<5> = <&mut StrArray<5>>::try_from(&mut *s).unwrap();
        sa.make_ascii_uppercase();
        assert_eq!(s, "HELLO");
    }

    #[test]
    fn test_try_from_mut_bytes() {
        let mut b = *b"hello";
        let sa: &mut StrArray<5> = <&mut StrArray<5>>::try_from(&mut b).unwrap();
        sa.make_ascii_uppercase();
        assert_eq!(sa, "HELLO");
    }

    #[test]
    fn test_from_strarray_for_str() {
        let s = str_array!("hello");
        let r: &str = (&s).into();
        assert_eq!(r, "hello");
    }

    #[test]
    fn test_from_mut_strarray_for_mut_str() {
        let mut s = str_array!("hello");
        let r: &mut str = (&mut s).into();
        r.make_ascii_uppercase();
        assert_eq!(r, "HELLO");
    }

    #[test]
    fn test_from_strarray_for_bytes() {
        let s = str_array!("hello");
        let r: &[u8; 5] = (&s).into();
        assert_eq!(r, b"hello");
    }

    #[test]
    fn test_from_strarray_for_byte_slice() {
        let s = str_array!("hello");
        let r: &[u8] = (&s).into();
        assert_eq!(r, b"hello");
    }
}

#[cfg(all(test, feature = "alloc"))]
mod alloc_tests {
    use super::*;
    use crate::str_array;

    use ::alloc::{boxed::Box, rc::Rc, string::String, sync::Arc};

    #[test]
    fn test_try_from_string() {
        let s = String::from("hello");
        let sa: StrArray<5> = s.try_into().unwrap();
        assert_eq!(sa, "hello");
    }

    #[test]
    fn test_try_from_box_str() {
        let s = String::from("hello").into_boxed_str();
        let sa: StrArray<5> = s.try_into().unwrap();
        assert_eq!(sa, "hello");
    }

    #[test]
    fn test_try_from_rc_str() {
        let s: Rc<str> = "hello".into();
        let sa: StrArray<5> = s.try_into().unwrap();
        assert_eq!(sa, "hello");
    }

    #[test]
    fn test_try_from_arc_str() {
        let s: Arc<str> = "hello".into();
        let sa: StrArray<5> = s.try_into().unwrap();
        assert_eq!(sa, "hello");
    }

    #[test]
    fn test_into_string() {
        let s = str_array!("hello");
        let string: String = s.into();
        assert_eq!(string, "hello");
    }

    #[test]
    fn test_into_box_str() {
        let s = str_array!("hello");
        let b: Box<str> = s.into();
        assert_eq!(&*b, "hello");
    }

    #[test]
    fn test_into_rc_str() {
        let s = str_array!("hello");
        let r: Rc<str> = s.into();
        assert_eq!(&*r, "hello");
    }

    #[test]
    fn test_into_arc_str() {
        let s = str_array!("hello");
        let a: Arc<str> = s.into();
        assert_eq!(&*a, "hello");
    }
}
