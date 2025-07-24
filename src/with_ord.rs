use crate::*;

use std::cmp::Ordering;

// Takes the `Ord` from U, but reverses it.
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct WithOrd<T: Eq, U: Ord>(pub T, pub U);

impl<T: Eq, U: Ord> PartialOrd for WithOrd<T, U> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.1.partial_cmp(&other.1)
    }
}
impl<T: Eq, U: Ord> Ord for WithOrd<T, U> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

