mod core;
pub use core::*;

mod mysynth;
pub use mysynth::*;

mod with_ord;
pub use with_ord::*;

mod examples;
pub use examples::*;

mod parser;
pub use parser::*;

mod fmt;

pub type Map<K, V> = indexmap::IndexMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    let s = std::fs::read_to_string("qm_neg_eq_2.sl").unwrap();
    let parsed = parse_sygus(&s);
    dbg!(&parsed);

    let (problem, oracle) = qm_neg_eq_2();
    println!("Answer: {:?}", cegis(problem, MySynth, oracle));
}
