use super::*;
use core::cmp::Ordering;

impl<const N: usize> PartialOrd<str> for StrArray<N> {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<const N: usize> PartialOrd<&str> for StrArray<N> {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        self.as_str().partial_cmp(*other)
    }
}

impl<const N: usize> PartialOrd<StrArray<N>> for str {
    fn partial_cmp(&self, other: &StrArray<N>) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<const N: usize> PartialOrd<StrArray<N>> for &str {
    fn partial_cmp(&self, other: &StrArray<N>) -> Option<Ordering> {
        (*self).partial_cmp(other.as_str())
    }
}

impl<const N: usize> PartialEq<str> for StrArray<N> {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl<const N: usize> PartialEq<&str> for StrArray<N> {
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl<const N: usize> PartialEq<StrArray<N>> for str {
    fn eq(&self, other: &StrArray<N>) -> bool {
        self.eq(other.as_str())
    }
}

impl<const N: usize> PartialEq<StrArray<N>> for &str {
    fn eq(&self, other: &StrArray<N>) -> bool {
        (*self).eq(other.as_str())
    }
}

#[cfg(test)]
mod tests {
    use crate::str_array;

    #[test]
    fn test_eq_ord_impls() {
        let a = str_array!("hello");
        let b = str_array!("yello");
        assert_ne!(a, b);
        assert_eq!(a, "hello");
        assert_eq!(a, *"hello");
        assert_eq!(&a, "hello");
        assert_eq!("hello", a);
        assert_eq!(*"hello", a);
        assert_eq!("hello", &a);
        assert!(a < b);
        assert!(a > "fizz");
        assert!("fizz" <= a);
        assert!(a < *"yeet");
        assert!(*"yeet" >= a);
        assert!(&a > "apple");
        assert!("apple" <= &a);
    }
}