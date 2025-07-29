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

    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Mod([Id; 2]),

    Abs([Id; 1]),

    Ite([Id; 3]),

    Lt([Id; 2]),
    Lte([Id; 2]),
    Gte([Id; 2]),
    Gt([Id; 2]),
    Equals([Id; 2]),

    Constant(Int),
}

impl Node {
    pub fn children(&self) -> &[Id] {
        match self {
            Node::Var(_) | Node::Constant(_) => &[],
            Node::Abs(s) => s,
            Node::Add(s) | Node::Sub(s) | Node::Mul(s) | Node::Div(s) | Node::Mod(s) | Node::Lt(s) | Node::Gt(s) | Node::Lte(s) | Node::Gte(s) | Node::Equals(s) => s,
            Node::Ite(s) => s,
        }
    }

    pub fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Node::Var(_) | Node::Constant(_) => &mut [],
            Node::Abs(s) => s,
            Node::Add(s) | Node::Sub(s) | Node::Mul(s) | Node::Div(s) | Node::Mod(s) | Node::Lt(s) | Node::Gt(s) | Node::Lte(s) | Node::Gte(s) | Node::Equals(s) => s,
            Node::Ite(s) => s,
        }
    }

    pub fn signature(&self) -> &'static (&'static [Ty], Ty) {
        match self {
            Node::Var(_) | Node::Constant(_) => &(&[], Ty::Int),
            Node::Add(_) | Node::Sub(_) | Node::Mul(_) | Node::Div(_) | Node::Mod(_) => &(&[Ty::Int; 2], Ty::Int),
            Node::Lt(_) | Node::Lte(_) | Node::Gte(_) | Node::Gt(_) | Node::Equals(_) => &(&[Ty::Int; 2], Ty::Bool),
            Node::Ite(_) => &(&[Ty::Bool, Ty::Int, Ty::Int], Ty::Int),
            Node::Abs(_) => &(&[Ty::Int], Ty::Int),
        }
    }

    pub fn ty(&self) -> Ty {
        let (args, ret) = self.signature();
        *ret
    }
}

pub struct Term {
    pub elems: Vec<Node>,
}

impl Term {
    pub fn push(&mut self, n: Node) {
        self.elems.push(n);
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
        Node::Lt([l, r]) => Value::Bool(to_int(ch(*l)) < to_int(ch(*r))),
        Node::Lte([l, r]) => Value::Bool(to_int(ch(*l)) <= to_int(ch(*r))),
        Node::Gt([l, r]) => Value::Bool(to_int(ch(*l)) > to_int(ch(*r))),
        Node::Gte([l, r]) => Value::Bool(to_int(ch(*l)) >= to_int(ch(*r))),
        Node::Equals([l, r]) => Value::Bool(to_int(ch(*l)) == to_int(ch(*r))),

        Node::Abs([x]) => Value::Int(to_int(ch(*x)).abs()),

        Node::Constant(i) => Value::Int(*i),
    }
}

pub fn eval_term(term: &Term, sigma: &Sigma) -> Value {
    let mut vals: Vec<Value> = Vec::new();
    for n in &term.elems {
        let f = |i: usize| vals[i].clone();
        vals.push(eval_node(n, sigma, &f));
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
            sigmas.push(sigma);
        } else {
            return term;
        }
    }
}
