use crate::*;

type Int = i64; // TODO add bigint.

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Int(Int),
    Bool(bool),
}

pub type Var = usize;

define_language! {
    pub enum Term {
        Var(Var),

        "add" = Add([Id; 2]),
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),

        "ite" = Ite([Id; 3]),
        "lt" = Lt([Id; 2]),
    }
}

pub type Sigma = Vec<Value>;

pub trait Problem {
    fn num_vars(&self) -> usize;
    fn sat(&self, val: &Value, sigma: &Sigma) -> bool;
}

pub trait Oracle {
    fn verify(&self, term: &RecExpr<Term>) -> Option<Sigma>;
}

pub trait Synth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> RecExpr<Term>;
}

fn to_int(v: Value) -> Int {
    match v {
        Value::Int(i) => i,
        _ => panic!("to_int failed"),
    }
}

fn to_bool(v: Value) -> bool {
    match v {
        Value::Bool(b) => b,
        _ => panic!("to_int failed"),
    }
}

pub fn eval_step(term: &Term, sigma: &Sigma, ch: &impl Fn(Id) -> Value) -> Value {
    match term {
        Term::Var(s) => sigma[*s].clone(),
        Term::Add([l, r]) => Value::Int(to_int(ch(*l)) + to_int(ch(*r))),
        Term::Mul([l, r]) => Value::Int(to_int(ch(*l)) * to_int(ch(*r))),
        Term::Sub([l, r]) => Value::Int(to_int(ch(*l)) - to_int(ch(*r))),
        Term::Div([l, r]) => {
            let l = to_int(ch(*l));
            let r = to_int(ch(*r));
            if r == 0 { Value::Int(0) } // NOTE: division by zero is zero for now.
            else { Value::Int(l / r) }
        },
        Term::Ite([cond, then, else_]) => {
            if to_bool(ch(*cond)) {
                ch(*then).clone()
            } else {
                ch(*else_).clone()
            }
        },
        Term::Lt([l, r]) => Value::Bool(to_int(ch(*l)) < to_int(ch(*r))),
    }
}

pub fn eval_term(term: &RecExpr<Term>, sigma: &Sigma) -> Value {
    let mut vals: Vec<Value> = Vec::new();
    for t in &*term {
        let f = |i| vals[usize::from(i)].clone();
        vals.push(eval_step(t, sigma, &f));
    }
    vals.last().unwrap().clone()
}

pub fn cegis(problem: impl Problem, mut synth: impl Synth, oracle: impl Oracle) -> RecExpr<Term> {
    let mut sigmas = Vec::new();
    loop {
        let term = synth.synth(&problem, &sigmas);
        dbg!(&term);
        // TODO check this later: assert!(problem.sat(&..., &sigmas));

        if let Some(sigma) = oracle.verify(&term) {
            dbg!(&sigma);
            sigmas.push(sigma);
        } else {
            return term;
        }
    }
}
