use crate::*;

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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty { Int, Bool }

impl Ty {
    pub fn to_string(&self) -> &'static str {
        match self {
            Ty::Int => "Int",
            Ty::Bool => "Bool",
        }
    }
}

impl Node {
    pub fn ty(&self) -> Ty {
        let (args, ret) = self.signature();
        *ret
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
        let i = self.elems.len();
        for mut n in t.elems {
            for x in n.children_mut() { *x += i; }
            self.push(n);
        }

        self.elems.len() - 1
    }
}

pub type Sigma = Vec<Value>;

pub fn to_int(v: Value) -> Int {
    match v {
        Value::Int(i) => i,
        _ => panic!("to_int failed"),
    }
}

pub fn to_bool(v: Value) -> bool {
    match v {
        Value::Bool(b) => b,
        _ => panic!("to_int failed"),
    }
}

pub fn eval_term(term: &Term, sigma: &Sigma) -> Value {
    let mut vals: Vec<Value> = Vec::new();
    for n in &term.elems {
        let f = |i: usize| vals[i].clone();
        vals.push(n.eval(&f, sigma));
    }
    vals.last().unwrap().clone()
}

pub fn eval_term_partial(i: Id, term: &[Node], sigma: &Sigma) -> Value {
    let f = |id: Id| eval_term_partial(id, term, sigma);
    term[i].eval(&f, sigma)
}

pub fn cegis(problem: &Problem) -> Term {
    let mut sigmas = Vec::new();
    loop {
        let term = synth(problem, &sigmas);
        println!("Candidate: {}", term_to_z3(&term, &problem.vars));
        // TODO check this later: assert!(problem.sat(&..., &sigmas));

        if let Some(sigma) = problem.verify(&term) {
            println!("CE: {:?}", &sigma);
            if sigmas.contains(&sigma) {
                panic!("This is broken!");
            }
            sigmas.push(sigma);
        } else {
            return term;
        }
    }
}
