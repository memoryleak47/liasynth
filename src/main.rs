mod core;
pub use core::*;

mod synth;
pub use synth::*;

mod with_ord;
pub use with_ord::*;

mod parser;
pub use parser::*;

mod sygus;
pub use sygus::*;

mod fmt;
pub use fmt::*;

pub type Map<K, V> = fxhash::FxHashMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    let arg = std::env::args().nth(1).unwrap_or(String::from("examples/max2_swap_renamed.sl"));
    let problem = mk_sygus_problem(&arg);

    let term = cegis(&problem);
    println!("Answer: {}", term_to_z3(&term, &problem.vars));
}
