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

#[derive(Clone, Debug)]
pub enum Node {
    Var(Var),

    // https://smt-lib.org/theories-Ints.shtml
    ConstInt(Int),
    Neg([Id; 1]),
    Sub([Id; 2]),
    Add([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Mod([Id; 2]),
    Abs([Id; 1]),

    Lt([Id; 2]),
    Lte([Id; 2]),
    Gte([Id; 2]),
    Gt([Id; 2]),

    // https://smt-lib.org/theories-Core.shtml
    True,
    False,
    Not([Id; 1]),
    Implies([Id; 2]),
    And([Id; 2]),
    Or([Id; 2]),
    Xor([Id; 2]),
    Equals([Id; 2]),
    Distinct([Id; 2]),
    Ite([Id; 3]),

    SynthCall(Box<[Id]>),
}

impl Node {
    pub fn children(&self) -> &[Id] {
        use Node::*;
        match self {
            Var(_) | ConstInt(_) | True | False => &[],
            Abs(s) | Neg(s) | Not(s) => s,
            Add(s) | Sub(s) | Mul(s) | Div(s) | Mod(s) | Lt(s) | Gt(s) | Lte(s) | Gte(s) | Equals(s) | Distinct(s) | Implies(s) | And(s) | Or(s) | Xor(s) => s,
            Ite(s) => s,
            SynthFun => &[],
        }
    }

    pub fn children_mut(&mut self) -> &mut [Id] {
        use Node::*;
        match self {
            Var(_) | ConstInt(_) | True | False => &mut [],
            Abs(s) | Neg(s) | Not(s) => s,
            Add(s) | Sub(s) | Mul(s) | Div(s) | Mod(s) | Lt(s) | Gt(s) | Lte(s) | Gte(s) | Equals(s) | Distinct(s) | Implies(s) | And(s) | Or(s) | Xor(s) => s,
            Ite(s) => s,
            SynthFun => &mut [],
        }
    }

    pub fn signature(&self) -> &'static (&'static [Ty], Ty) {
        use Node::*;
        match self {
            Var(_) | ConstInt(_) | True | False => &(&[], Ty::Int),
            Add(_) | Sub(_) | Mul(_) | Div(_) | Mod(_) => &(&[Ty::Int; 2], Ty::Int),
            Lt(_) | Lte(_) | Gte(_) | Gt(_) | Equals(_) => &(&[Ty::Int; 2], Ty::Bool),
            Ite(_) => &(&[Ty::Bool, Ty::Int, Ty::Int], Ty::Int),
            Neg(_) => &(&[Ty::Int], Ty::Int),
            Not(_) => &(&[Ty::Bool], Ty::Bool),
            Implies(_) | And(_) | Or(_) | Xor(_) | Distinct(_) => &(&[Ty::Bool; 2], Ty::Bool),
            Abs(_) => &(&[Ty::Int], Ty::Int),
            SynthFun => &(&[Ty::Int], Ty::Int), //?
        }
    }

    pub fn ty(&self) -> Ty {
        let (args, ret) = self.signature();
        *ret
    }
}

#[derive(Clone)]
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

pub trait Problem {
    fn prod_rules(&self) -> &[Node];
    fn sat(&self, term: &Term, sigma: &Sigma) -> bool;
    fn accesses(&self) -> &[Box<[Var]>];
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

pub fn eval_node(node: &Node, sigma: &Sigma, ch: &impl Fn(Id) -> Value, synthfun: &Term) -> Value {
    match node {
        Node::Var(s) => sigma[*s].clone(),
        Node::Add([l, r]) => Value::Int(to_int(ch(*l)) + to_int(ch(*r))),
        Node::Mul([l, r]) => Value::Int(to_int(ch(*l)) * to_int(ch(*r))),
        Node::Sub([l, r]) => Value::Int(to_int(ch(*l)) - to_int(ch(*r))),
        Node::Mod([l, r]) => Value::Int(to_int(ch(*l)) % to_int(ch(*r))),
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
        Node::True => Value::Bool(true),
        Node::False => Value::Bool(false),
        Node::Neg([x]) => Value::Int(-to_int(ch(*x))),
        Node::Not([x]) => Value::Bool(!to_bool(ch(*x))),
        Node::Lt([l, r]) => Value::Bool(to_int(ch(*l)) < to_int(ch(*r))),
        Node::Lte([l, r]) => Value::Bool(to_int(ch(*l)) <= to_int(ch(*r))),
        Node::Gt([l, r]) => Value::Bool(to_int(ch(*l)) > to_int(ch(*r))),
        Node::Gte([l, r]) => Value::Bool(to_int(ch(*l)) >= to_int(ch(*r))),
        Node::Equals([l, r]) => Value::Bool(ch(*l) == ch(*r)),
        Node::Distinct([l, r]) => Value::Bool(ch(*l) != ch(*r)),

        Node::And([l, r]) => Value::Bool(to_bool(ch(*l)) && to_bool(ch(*r))),
        Node::Or([l, r]) => Value::Bool(to_bool(ch(*l)) || to_bool(ch(*r))),
        Node::Xor([l, r]) => Value::Bool(to_bool(ch(*l)) != to_bool(ch(*r))),
        Node::Implies([l, r]) => Value::Bool(!to_bool(ch(*l)) || to_bool(ch(*r))),

        Node::Abs([x]) => Value::Int(to_int(ch(*x)).abs()),

        Node::ConstInt(i) => Value::Int(*i),
        Node::SynthCall(args) => {
            let sigma = args.iter().map(|x| ch(*x)).collect();
            eval_term(synthfun, &sigma, synthfun)
        },
    }
}

pub fn eval_term(term: &Term, sigma: &Sigma, synthfun: &Term) -> Value {
    let mut vals: Vec<Value> = Vec::new();
    for n in &term.elems {
        let f = |i: usize| vals[i].clone();
        vals.push(eval_node(n, sigma, &f, synthfun));
    }
    vals.last().unwrap().clone()
}

pub fn cegis(problem: impl Problem, mut synth: impl Synth, oracle: impl Oracle) -> Term {
    let mut sigmas = Vec::new();
    loop {
        let term = synth.synth(&problem, &sigmas);
        println!("Candidate: {:?}", &term);
        // TODO check this later: assert!(problem.sat(&..., &sigmas));

        if let Some(sigma) = oracle.verify(&term) {
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
