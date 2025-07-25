use crate::*;

pub struct MySynth;

type Score = usize;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

enum Ty { Int, Bool }

struct Ctxt<'a, P> {
    queue: Queue, // contains ids of pending (i.e. not solidifed Ids), or solid Ids which got an updated size.
    sigmas: &'a [Sigma],
    problem: &'a P,

    vals_lookup: Map<Box<[Value]>, Id>,
    classes: Vec<Class>,

    i_solids: Vec<Id>,
    b_solids: Vec<Id>,

    out: Option<Id>,
}

struct Class {
    node: Node,
    size: usize,
    vals: Box<[Value]>,
    handled_size: Option<usize>, // what was the size when this class was handled last time.
}

fn run<'a, P: Problem>(ctxt: &mut Ctxt<P>) -> Term {
    for v in 0..ctxt.problem.num_vars() {
        add_node(Node::Var(v), ctxt);
    }

    for &c in ctxt.problem.constants() {
        add_node(Node::Constant(c), ctxt);
    }

    while let Some(WithOrd(x, _)) = ctxt.queue.pop() {
        // dbg!(extract(x, ctxt));
        handle(x, ctxt);

        if let Some(x) = ctxt.out {
            return extract(x, ctxt);
        }
    }

    panic!("No term found!")
}

// makes "x" solid if it's not solid yet.
fn handle<'a, P: Problem>(x: Id, ctxt: &mut Ctxt<P>) {
    let c = &mut ctxt.classes[x];

    // if the current size is the same size of the last "handle" call, nothing it to be done.
    if c.handled_size == Some(c.size) { return; }

    if c.handled_size.is_none() {
        match node_ty(&c.node) {
            Ty::Int => &mut ctxt.i_solids,
            Ty::Bool => &mut ctxt.b_solids,
        }.push(x);
    }

    c.handled_size = Some(c.size);

    grow(x, ctxt);
}

fn grow<'a, P: Problem>(x: Id, ctxt: &mut Ctxt<P>) {
    let ty = node_ty(&ctxt.classes[x].node);
    match ty {
        Ty::Int => {
            let i_solids = ctxt.i_solids.clone();
            let b_solids = ctxt.b_solids.clone();

            for &y in &i_solids {
                add_node(Node::Add([x, y]), ctxt);
                add_node(Node::Add([y, x]), ctxt);

                add_node(Node::Sub([x, y]), ctxt);
                add_node(Node::Sub([y, x]), ctxt);

                add_node(Node::Mul([x, y]), ctxt);
                add_node(Node::Mul([y, x]), ctxt);

                add_node(Node::Div([x, y]), ctxt);
                add_node(Node::Div([y, x]), ctxt);

                add_node(Node::Lt([x, y]), ctxt);
                add_node(Node::Lt([y, x]), ctxt);

                for &cond in &b_solids {
                    add_node(Node::Ite([cond, x, y]), ctxt);
                    add_node(Node::Ite([cond, y, x]), ctxt);
                }
            }
        },
        Ty::Bool => {
            let i_solids = ctxt.i_solids.clone();

            for &y in &i_solids {
                for &z in &i_solids {
                    add_node(Node::Ite([x, y, z]), ctxt);
                }
            }
        },
    }
}

impl Synth for MySynth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> Term {
        run(&mut Ctxt {
            queue: Default::default(),
            sigmas,
            problem,
            vals_lookup: Default::default(),
            classes: Vec::new(),
            i_solids: Vec::new(),
            b_solids: Vec::new(),
            out: None,
        })
    }
}

fn add_node<'a, P: Problem>(node: Node, ctxt: &mut Ctxt<'a, P>) {
    let vals = vals(&node, ctxt);
    if let Some(&i) = ctxt.vals_lookup.get(&vals) {
        let newsize = minsize(&node, ctxt);
        let c = &mut ctxt.classes[i];
        if newsize < c.size {
            c.size = newsize;
            c.node = node.clone();
            enqueue(i, ctxt);
        }
    } else {
        let i = ctxt.classes.len();

        // write to `out`, if this [Value] was successful.
        if ctxt.sigmas.iter().zip(vals.iter()).all(|(sigma, val)| ctxt.problem.sat(val, sigma)) {
            ctxt.out = Some(i);
        }

        ctxt.classes.push(Class {
            size: minsize(&node, ctxt),
            node,
            vals: vals.clone(),
            handled_size: None,
        });
        ctxt.vals_lookup.insert(vals, i);
        enqueue(i, ctxt);
    }
}

fn enqueue<'a, P: Problem>(x: Id, ctxt: &mut Ctxt<P>) {
    let h = heuristic(x, ctxt);
    ctxt.queue.push(WithOrd(x, h));
}

fn heuristic<'a, P: Problem>(x: Id, ctxt: &Ctxt<'a, P>) -> Score {
    let c = &ctxt.classes[x];

    if let Ty::Bool = node_ty(&c.node) {
        return 10000;
    }

    let satcount = satcount(&c.vals, ctxt);

    let mut a = 100000;
    for _ in satcount..ctxt.sigmas.len() {
        a /= 2;
    }

    a / (c.size + 5)
}

fn vals<'a, P: Problem>(node: &Node, ctxt: &Ctxt<'a, P>) -> Box<[Value]> {
    ctxt.sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |id: Id| ctxt.classes[id].vals[i].clone();
        eval_node(node, sigma, &f)
    }).collect::<Box<[_]>>()
}

fn minsize<'a, P: Problem>(node: &Node, ctxt: &Ctxt<'a, P>) -> usize {
    node.children().iter().map(|x| ctxt.classes[*x].size).sum::<usize>() + 1
}

fn satcount<'a, P: Problem>(vals: &[Value], ctxt: &Ctxt<'a, P>) -> usize {
    let it = vals.iter().zip(ctxt.sigmas);
    it.filter(|(val, sigma)| ctxt.problem.sat(val, sigma))
      .count()
}

fn node_ty(node: &Node) -> Ty {
    match node {
        Node::Var(_) | Node::Add(_) | Node::Sub(_) | Node::Mul(_) | Node::Div(_) | Node::Ite(_) | Node::Constant(_) => Ty::Int,
        Node::Lt(_) => Ty::Bool,
    }
}

fn extract<'a, P: Problem>(x: Id, ctxt: &Ctxt<'a, P>) -> Term {
    let mut t = Term { elems: Vec::new() };
    match ctxt.classes[x].node {
        Node::Var(v) => { t.push(Node::Var(v)); },
        Node::Add([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Add([x, y]));
        },
        Node::Sub([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Sub([x, y]));
        },
        Node::Mul([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Mul([x, y]));
        },
        Node::Div([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Div([x, y]));
        },
        Node::Lt([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Lt([x, y]));
        },
        Node::Ite([x, y, z]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            let z = t.push_subterm(extract(z, ctxt));
            t.push(Node::Ite([x, y, z]));
        },
        Node::Constant(i) => { t.push(Node::Constant(i)); },
    }
    t
}
