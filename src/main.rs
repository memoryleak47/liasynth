pub use egg::{Extractor, EGraph, RecExpr, Id, define_language, Analysis, DidMerge, AstSize, Language};

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

mod fmt;

pub type Map<K, V> = indexmap::IndexMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    let (problem, oracle) = max_n(3);
    dbg!(cegis(problem, MySynth, oracle));
}
