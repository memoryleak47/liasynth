mod core;
pub use core::*;

mod synth;
pub use synth::*;

mod satcount;
pub use satcount::*;

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

mod linearreg;
pub use linearreg::BayesianLinearRegression;

mod termembed;
pub use termembed::TermEmbedder;

#[macro_use]
mod phase_timing;
use phase_timing::{ReportOnDrop, init_timing_hooks};

pub type Map<K, V> = fxhash::FxHashMap<K, V>;
pub use std::collections::BinaryHeap;

fn main() {
    // init_timing_hooks();
    // let _report = ReportOnDrop;

    let arg = std::env::args().nth(1).unwrap_or_else(|| {
        "examples/RF_no_assumptions/ChenFlurMukhopadhyaySAS2012Ex206RFSynt.noassumptions.sl"
            .to_string()
    });
    let problem = mk_sygus_problem(&arg);

    match cegis(&problem) {
        Some(term) => {
            let vars = problem.vars.keys().cloned().collect::<Box<[_]>>();
            println!("Answer: {}", term_to_z3(&term, &vars));
        }
        None => {}
    }
}
