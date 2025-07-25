use crate::*;

type Int = i64; // TODO add bigint.

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Int(Int),
    Bool(bool),
}

pub type Var = usize;
pub type Id = usize;

#[derive(Clone, Debug)]
pub enum Node {
    Var(Var),

    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),

    Ite([Id; 3]),
    Lt([Id; 2]),
}

impl Node {
    pub fn children(&self) -> Box<[Id]> {
        match self {
            Node::Var(_) => Box::new([]),
            Node::Add(s) | Node::Sub(s) | Node::Mul(s) | Node::Div(s) | Node::Lt(s) => Box::new(*s),
            Node::Ite(s) => Box::new(*s),
        }
    }

    pub fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Node::Var(_) => &mut [],
            Node::Add(s) | Node::Sub(s) | Node::Mul(s) | Node::Div(s) | Node::Lt(s) => s,
            Node::Ite(s) => s,
        }
    }
}

#[derive(Debug)]
pub struct Term {
    pub elems: Vec<Node>,
}

impl Term {
    pub fn push(&mut self, n: Node) {
        self.elems.push(n);
    }

    pub fn push_subterm(&mut self, mut t: Term) -> Id {
        let i = self.elems.len();
        for mut n in t.elems {
            for x in n.children_mut() { *x += i; }
            self.push(n);
        }

        self.elems.len()
    }
}

pub type Sigma = Vec<Value>;

pub trait Problem {
    fn num_vars(&self) -> usize;
    fn sat(&self, val: &Value, sigma: &Sigma) -> bool;
}

pub trait Oracle {
    fn verify(&self, term: &Term) -> Option<Sigma>;
}

pub trait Synth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> Term;
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

pub fn eval_node(node: &Node, sigma: &Sigma, ch: &impl Fn(Id) -> Value) -> Value {
    match node {
        Node::Var(s) => sigma[*s].clone(),
        Node::Add([l, r]) => Value::Int(to_int(ch(*l)) + to_int(ch(*r))),
        Node::Mul([l, r]) => Value::Int(to_int(ch(*l)) * to_int(ch(*r))),
        Node::Sub([l, r]) => Value::Int(to_int(ch(*l)) - to_int(ch(*r))),
        Node::Div([l, r]) => {
            let l = to_int(ch(*l));
            let r = to_int(ch(*r));
            if r == 0 { Value::Int(0) } // NOTE: division by zero is zero for now.
            else { Value::Int(l / r) }
        },
        Node::Ite([cond, then, else_]) => {
            if to_bool(ch(*cond)) {
                ch(*then).clone()
            } else {
                ch(*else_).clone()
            }
        },
        Node::Lt([l, r]) => Value::Bool(to_int(ch(*l)) < to_int(ch(*r))),
    }
}

pub fn eval_term(term: &Term, sigma: &Sigma) -> Value {
    let mut vals: Vec<Value> = Vec::new();
    for n in &term.elems {
        let f = |i| vals[usize::from(i)].clone();
        vals.push(eval_node(n, sigma, &f));
    }
    vals.last().unwrap().clone()
}

pub fn cegis(problem: impl Problem, mut synth: impl Synth, oracle: impl Oracle) -> Term {
    let mut sigmas = Vec::new();
    loop {
        let term = synth.synth(&problem, &sigmas);
        // println!("Candidate: {}", &term);
        // TODO check this later: assert!(problem.sat(&..., &sigmas));

        if let Some(sigma) = oracle.verify(&term) {
            // println!("CE: {:?}", &sigma);
            sigmas.push(sigma);
        } else {
            return term;
        }
    }
}
