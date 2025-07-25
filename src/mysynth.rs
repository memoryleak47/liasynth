use crate::*;

pub struct MySynth;

type Score = usize;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

enum Ty { Int, Bool }

struct Ctxt<'a, P> {
    queue: Queue,
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

    while let Some(WithOrd(x, _)) = ctxt.queue.pop() {
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
            if c.handled_size.is_some() {
                handle(i, ctxt);
            }
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
    }
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

fn node_ty(node: &Node) -> Ty {
    match node {
        Node::Var(_) | Node::Add(_) | Node::Sub(_) | Node::Mul(_) | Node::Div(_) | Node::Ite(_) => Ty::Int,
        Node::Lt(_) => Ty::Bool,
    }
}

fn extract<'a, P: Problem>(x: Id, ctxt: &Ctxt<'a, P>) -> Term {
    todo!()
}
