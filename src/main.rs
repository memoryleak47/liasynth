pub use egg::*;

mod core;
pub use core::*;

mod g;
pub use g::*;

mod mysynth;
pub use mysynth::*;

mod with_ord;
pub use with_ord::*;

mod examples;
pub use examples::*;

pub type Map<K, V> = indexmap::IndexMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
}
