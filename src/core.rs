use crate::*;

use once_cell::sync::Lazy;
use std::sync::Mutex;

pub struct Stats {
    pub programs_generated: usize,
    pub new_programs_generated: usize,
    pub programs_checked: usize,
    pub counterexamples: usize,
}

impl Stats {
    pub fn print(&self) {
        eprintln!(
            "\n== Synthesis stats ==\n\
             programs_generated:     {}\n\
             new_programs_generated: {}\n\
             programs_checked:       {}\n\
             counterexamples:        {}",
            self.programs_generated,
            self.new_programs_generated,
            self.programs_checked,
            self.counterexamples
        );
    }
}
impl Default for Stats {
    fn default() -> Self {
        Self {
            programs_generated: 0,
            new_programs_generated: 0,
            programs_checked: 0,
            counterexamples: 0,
        }
    }
}

pub static GLOBAL_STATS: Lazy<Mutex<Stats>> = Lazy::new(|| Mutex::new(Stats::default()));

pub type Int = i64; // TODO add bigint.

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Int(Int),
    Bool(bool),
}

impl Value {
    pub fn ty(&self) -> Ty {
        match self {
            Value::Int(_) => Ty::Int,
            Value::Bool(_) => Ty::Bool,
        }
    }
}

pub type Var = usize;
pub type Id = usize;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Ty {
    Int,
    Bool,
    NonTerminal(usize),
    PRule(usize),
}

impl Ty {
    pub fn to_string(&self) -> &'static str {
        match self {
            Ty::Int => "Int",
            Ty::Bool => "Bool",
            Ty::NonTerminal(_) => "",
            Ty::PRule(_) => "",
        }
    }

    pub fn into_nt(&self) -> Option<usize> {
        match self {
            Ty::NonTerminal(s) => Some(*s),
            Ty::PRule(s) => Some(s.trailing_zeros() as usize),
            _ => None,
        }
    }
    pub fn captures_ty(&self, other: &Ty) -> bool {
        match (self, other) {
            (Ty::PRule(mask), Ty::NonTerminal(n)) => (mask & (1usize << n)) != 0,
            _ => false,
        }
    }

    pub fn nt_indices(&self) -> Vec<usize> {
        match self {
            Ty::PRule(mask) => {
                let mut bits = *mask;
                let mut out = Vec::new();
                while bits != 0 {
                    let i = bits.trailing_zeros() as usize;
                    out.push(i);
                    bits &= bits - 1; // clear the lowest set bit
                }
                out
            }
            _ => Vec::new(),
        }
    }
}

impl Node {
    pub fn ty(&self) -> Ty {
        let (args, ret) = self.signature();
        ret
    }
}

#[derive(Clone, Debug)]
pub struct Term {
    pub elems: Vec<Node>,
}

impl Term {
    pub fn push(&mut self, n: Node) -> Id {
        self.elems.push(n);

        self.elems.len() - 1
    }

    pub fn push_subterm(&mut self, t: Term) -> Id {
        let base = self.elems.len();

        for mut n in t.elems.into_iter() {
            for ch in n.children_mut().iter_mut() {
                if let Child::Hole(j, ref mut idx) = *ch {
                    *idx += base;
                }
            }
            self.elems.push(n);
        }

        self.elems.len() - 1
    }
}

pub type Sigma = Vec<Value>;

pub fn to_int(v: Value) -> Int {
    match v {
        Value::Int(i) => i,
        _ => panic!("to_int failed on val {:?}", v),
    }
}

pub fn to_bool(v: Value) -> bool {
    match v {
        Value::Bool(b) => b,
        _ => panic!("to_bool failed on val {:?}", v),
    }
}

pub fn eval_term(term: &Term, sigma: &Sigma) -> Option<Value> {
    let mut vals: Vec<Value> = Vec::new();
    for n in &term.elems {
        let f = |i: usize| Some(vals[i].clone());
        vals.push(n.eval(&f, sigma)?);
    }
    Some(vals.last().unwrap().clone())
}

pub fn eval_term_partial(i: Id, term: &[Node], sigma: &Sigma) -> Option<Value> {
    let f = |id: Id| eval_term_partial(id, term, sigma);
    term[i].eval(&f, sigma)
}

pub fn cegis(problem: &Problem) -> Term {
    let mut sigmas = Vec::new();
    let mut cxs_cache = None;
    let mut classes = None;
    let embedding_dim = 5;
    let mut term_embed = TermEmbedder::new(embedding_dim);
    let mut olinr = BayesianLinearRegression::with_default(embedding_dim + 3, 50);
    loop {
        let (term, cxsc, clss) = synth(
            problem,
            &sigmas,
            cxs_cache,
            classes,
            &mut term_embed,
            &mut olinr,
        );
        classes = Some(clss);
        cxs_cache = Some(cxsc);
        // println!(
        //     "Candidate: {}",
        //     term_to_z3(&term, &problem.vars.keys().cloned().collect::<Box<[_]>>())
        // );

        GLOBAL_STATS.lock().unwrap().counterexamples += 1;
        // TODO check this later: assert!(problem.sat(&..., &sigmas));
        if let Some(sigma) = problem.verify(&term) {
            // println!("CE: {:?}", &sigma);
            if sigmas.contains(&sigma) {
                panic!("This is broken!");
            }
            sigmas.push(sigma);
        } else {
            return term;
        }
    }
}

fn init_sigmas(problem: &Problem) -> Vec<Sigma> {
    let mut sigmas = Vec::new();
    for i in 0..=problem.context_vars.len() {
        let sigma = problem
            .context_vars
            .iter()
            .enumerate()
            .map(|(i2, (v, ty))| match (i == i2, ty) {
                (b, Ty::Bool) => Value::Bool(b),
                (b, Ty::Int) => Value::Int(b as i64),
                _ => panic!("Should not happen"),
            })
            .collect();
        sigmas.push(sigma);
    }
    sigmas
}
