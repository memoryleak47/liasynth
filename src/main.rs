mod core;
pub use core::*;

mod synth;
pub use synth::*;

mod with_ord;
pub use with_ord::*;

mod parser;
pub use parser::*;

mod problem;
pub use problem::*;

mod fmt;
pub use fmt::*;

mod langdef;
pub use langdef::*;

mod perceptron;
pub use perceptron::*;

pub type Map<K, V> = fxhash::FxHashMap<K, V>;
pub use std::collections::BinaryHeap;


fn main() {
    let arg = std::env::args().nth(1).unwrap_or(String::from("examples/LIA/MPwL_d4s3.sl"));
    let problem = mk_sygus_problem(&arg);

    let term = cegis(&problem);
    println!("Answer: {}", term_to_z3(&term, &problem.vars.keys().cloned().collect::<Box<[_]>>()));
}
