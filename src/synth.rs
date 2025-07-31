use crate::*;

use itertools::Itertools;

type Score = usize;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

// SmallSigma has as many values as our synthfun has arguments.
// BigSigma has as many values as our Sygus file declares.
// HugeSigma is BigSigma extended by one variable per instantiation of the synthfun.

struct Ctxt<'a> {
    queue: Queue, // contains ids of pending (i.e. not solidifed Ids), or solid Ids which got an updated size.

    big_sigmas: &'a [Sigma],
    small_sigmas: Box<[Sigma]>,

    // for each big_sigma, this returns the list of small_sigmas corresponding to the instantiations of the synthfun.
    sigma_indices: Box<[Box<[usize]>]>,

    problem: &'a Problem,

    vals_lookup: Map<Box<[Value]>, Id>,
    classes: Vec<Class>,

    i_solids: Vec<Id>,
    b_solids: Vec<Id>,
}

struct Class {
    node: Node,
    size: usize,
    vals: Box<[Value]>,
    handled_size: Option<usize>, // what was the size when this class was handled last time.
    satcount: usize,
}

fn run(ctxt: &mut Ctxt) -> Term {
    for n in ctxt.problem.prod_rules() {
        let n = n.clone();
        if n.children().is_empty() {
            if let Some(sol) = add_node(n, ctxt) {
                return extract(sol, ctxt);
            }
        }
    }

    while let Some(WithOrd(x, _)) = ctxt.queue.pop() {
        if let Some(sol) = handle(x, ctxt) {
            return extract(sol, ctxt);
        }
    }

    panic!("No term found!")
}

// makes "x" solid if it's not solid yet.
fn handle(x: Id, ctxt: &mut Ctxt) -> Option<Id> {
    let c = &mut ctxt.classes[x];

    // if the current size is the same size of the last "handle" call, nothing it to be done.
    if c.handled_size == Some(c.size) { return None; }

    if c.handled_size.is_none() {
        match c.node.ty() {
            Ty::Int => &mut ctxt.i_solids,
            Ty::Bool => &mut ctxt.b_solids,
        }.push(x);
    }

    c.handled_size = Some(c.size);

    grow(x, ctxt)
}

fn grow(x: Id, ctxt: &mut Ctxt) -> Option<Id> {
    let ty = ctxt.classes[x].node.ty();

    for rule in ctxt.problem.prod_rules() {
        let (in_types, out_type) = rule.signature();
        for i in 0..rule.children().len() {
            let mut rule = rule.clone();
            if in_types[i] != ty { continue }
            rule.children_mut()[i] = x;
            let mut in_types: Vec<_> = in_types.iter().cloned().collect();
            in_types.remove(i);
            let it = in_types.iter().map(|ty| match ty {
                Ty::Int => ctxt.i_solids.clone().into_iter(),
                Ty::Bool => ctxt.b_solids.clone().into_iter(),
            });

            for a in it.multi_cartesian_product() {
                rule.children_mut().iter_mut().enumerate()
                    .filter(|(i2, _)| *i2 != i)
                    .map(|(_, x)| x)
                    .zip(a.iter()).for_each(|(ptr, v)| { *ptr = *v; });

                if let Some(sol) = add_node(rule.clone(), ctxt) {
                    return Some(sol);
                }
            }
        }
    }
    None
}

pub fn synth(problem: &Problem, big_sigmas: &[Sigma]) -> Term {
    let mut small_sigmas: Vec<Sigma> = Vec::new();
    let mut sigma_indices: Vec<Box<[usize]>> = Vec::new();
    for bsigma in big_sigmas.iter() {
        let mut indices: Vec<usize> = Vec::new();
        for a in problem.instvars.iter() {
            let ssigma: Sigma = a.iter().map(|i| eval_term_partial(*i, &problem.constraint.elems, &bsigma)).collect();
            small_sigmas.push(ssigma.clone());
            let idx = match small_sigmas.iter().position(|sigma2| sigma2 == &ssigma) {
                Some(i) => i,
                None => {
                    small_sigmas.push(ssigma);
                    small_sigmas.len() - 1
                },
            };
            indices.push(idx);
        }
        let indices: Box<[usize]> = indices.into();
        sigma_indices.push(indices);
    }
    let small_sigmas: Box<[Sigma]> = small_sigmas.into();
    let sigma_indices: Box<[Box<[usize]>]> = sigma_indices.into();

    run(&mut Ctxt {
        queue: Default::default(),
        big_sigmas,
        small_sigmas,
        sigma_indices,
        problem,
        vals_lookup: Default::default(),
        classes: Vec::new(),
        i_solids: Vec::new(),
        b_solids: Vec::new(),
    })
}

fn add_node(node: Node, ctxt: &mut Ctxt) -> Option<Id> {
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

        ctxt.classes.push(Class {
            size: minsize(&node, ctxt),
            node,
            vals: vals.clone(),
            handled_size: None,
            satcount: 0, // will be set later!
        });
        ctxt.vals_lookup.insert(vals, i);

        let satcount = satcount(i, ctxt);
        ctxt.classes[i].satcount = satcount;

        // dbg!(extract(i, ctxt));

        // if this [Value] was successful, return it.
        if satcount == ctxt.big_sigmas.len() {
            return Some(i);
        }

        enqueue(i, ctxt);
    }

    None
}

fn enqueue(x: Id, ctxt: &mut Ctxt) {
    let h = heuristic(x, ctxt);
    ctxt.queue.push(WithOrd(x, h));
}

fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    if let Ty::Bool = c.node.ty() {
        return 10000;
    }

    let mut a = 100000;
    let subterms = c.node.children();
    let max_subterm_satcount = subterms
        .iter()
        .map(|s| ctxt.classes[*s].satcount)
        .max()
        .unwrap_or_else(|| 0);


    let tmp = c.satcount.saturating_sub(max_subterm_satcount / 2);

    for _ in tmp..ctxt.big_sigmas.len() {
        a /= 2;
    }

    a / (c.size + 5)
}

fn vals(node: &Node, ctxt: &Ctxt) -> Box<[Value]> {
    ctxt.small_sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |id: Id| ctxt.classes[id].vals[i].clone();
        node.eval(&f, sigma)
    }).collect()
}

fn minsize(node: &Node, ctxt: &Ctxt) -> usize {
    node.children().iter().map(|x| ctxt.classes[*x].size).sum::<usize>() + 1
}

fn satcount(x: Id, ctxt: &mut Ctxt) -> usize {
    if ctxt.classes[x].node.ty() != ctxt.problem.rettype {
        return 0;
    }
    // TODO type-chk for arguments.

    // TODO re-add cx_value_cache.
    let mut count = 0;
    for i in 0..ctxt.big_sigmas.len() {
        let b = local_sat(i, x, ctxt);
        count += b as usize;
    }
    count
}

fn local_sat(big_sigma_idx: usize, class: Id, ctxt: &Ctxt) -> bool {
    let mut huge_sigma = ctxt.big_sigmas[big_sigma_idx].clone();
    let c = &ctxt.classes[class];
    let vals = &c.vals;

    let indices = &ctxt.sigma_indices[big_sigma_idx];
    for idx in indices.iter() {
        huge_sigma.push(vals[*idx].clone());
    }

    eval_term(&ctxt.problem.constraint, &huge_sigma) == Value::Bool(true)
}

fn extract(x: Id, ctxt: &Ctxt) -> Term {
    let mut t = Term { elems: Vec::new() };
    match ctxt.classes[x].node {
        Node::VarInt(v) => { t.push(Node::VarInt(v)); },
        Node::VarBool(v) => { t.push(Node::VarBool(v)); },
        Node::Add([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Add([x, y]));
        },
        Node::Implies([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Implies([x, y]));
        },
        Node::And([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::And([x, y]));
        },
        Node::Or([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Or([x, y]));
        },
        Node::Xor([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Xor([x, y]));
        },
        Node::Sub([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Sub([x, y]));
        },
        Node::Neg([x]) => {
            let x = t.push_subterm(extract(x, ctxt));
            t.push(Node::Neg([x]));
        },
        Node::Not([x]) => {
            let x = t.push_subterm(extract(x, ctxt));
            t.push(Node::Not([x]));
        },
        Node::True => { t.push(Node::True); },
        Node::False => { t.push(Node::False); },
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
        Node::Mod([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Mod([x, y]));
        },
        Node::Lt([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Lt([x, y]));
        },
        Node::Lte([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Lte([x, y]));
        },
        Node::Gt([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Gt([x, y]));
        },
        Node::Gte([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Gte([x, y]));
        },
        Node::Equals([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Equals([x, y]));
        },
        Node::Distinct([x, y]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            t.push(Node::Distinct([x, y]));
        },
        Node::Abs([x]) => {
            let x = t.push_subterm(extract(x, ctxt));
            t.push(Node::Abs([x]));
        },
        Node::Ite([x, y, z]) => {
            let x = t.push_subterm(extract(x, ctxt));
            let y = t.push_subterm(extract(y, ctxt));
            let z = t.push_subterm(extract(z, ctxt));
            t.push(Node::Ite([x, y, z]));
        },
        Node::ConstInt(i) => { t.push(Node::ConstInt(i)); },
    }
    t
}
