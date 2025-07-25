mod core;
pub use core::*;

mod mysynth;
pub use mysynth::*;

mod with_ord;
pub use with_ord::*;

mod examples;
pub use examples::*;

mod fmt;

pub type Map<K, V> = indexmap::IndexMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    let (problem, oracle) = x_lt_y();
    println!("Answer: {:?}", cegis(problem, MySynth, oracle));
}
