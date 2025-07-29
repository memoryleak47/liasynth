mod core;
pub use core::*;

mod mysynth;
pub use mysynth::*;

mod with_ord;
pub use with_ord::*;

// TODO re-add.
// mod examples;
// pub use examples::*;

mod parser;
pub use parser::*;

mod sygus;
pub use sygus::*;

mod fmt;

pub type Map<K, V> = fxhash::FxHashMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    let (problem, oracle) = sygus_problem("max4.sl");
    println!("Answer: {:?}", cegis(problem, MySynth, oracle));
}
