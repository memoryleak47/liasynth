use crate::*;

use ordered_float::OrderedFloat;
use itertools::Itertools;

type Score = OrderedFloat<f64>;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

// SmallSigma has as many values as our synthfun has arguments.
// BigSigma has as many values as our Sygus file declares.
// HugeSigma is BigSigma extended by one variable per instantiation of the synthfun.

// TODO:
//   -> Look in to incrememntal computation (propogating parts previously computed each time a new counterexample is found)
//   -> Frontier seach (reduces the memory burden by storing only the frontier nodes and not the previously searched nodes)
//     - https://dl.acm.org/doi/pdf/10.1145/1089023.1089024
struct Ctxt<'a> {
    queue: Queue, // contains ids of pending (i.e. not solidifed Ids), or solid Ids which got an updated size.

    big_sigmas: &'a [Sigma],
    small_sigmas: Box<[Sigma]>,

    // for each big_sigma, this returns the list of small_sigmas corresponding to the instantiations of the synthfun.
    sigma_indices: Box<[Box<[usize]>]>,

    problem: &'a Problem,

    // indexed by small-sigma.
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
            let (_, sol) = add_node(n, ctxt);
            if let Some(sol) = sol {
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

    let (maxsat, sol) = grow(x, ctxt);
    let X = get_features(x, ctxt);

    sol
}

fn grow(x: Id, ctxt: &mut Ctxt) -> (usize, Option<Id>) {
    let ty = ctxt.classes[x].node.ty();
    let mut max_satocunt = 0;

    for rule in ctxt.problem.prod_rules() {
        let (in_types, _out_type) = rule.signature();
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

                let (id, sol) = add_node(rule.clone(), ctxt);
                max_satocunt = std::cmp::max(max_satocunt, ctxt.classes[id].satcount);
                if let Some(sol) = sol {
                    return (max_satocunt, Some(sol));
                }
            }
        }
    }
    (max_satocunt, None)
}

pub fn synth(problem: &Problem, big_sigmas: &[Sigma]) -> Term {
    let mut small_sigmas: Vec<Sigma> = Vec::new();
    let mut sigma_indices: Vec<Box<[usize]>> = Vec::new();

    for bsigma in big_sigmas.iter() {
        let mut indices: Vec<usize> = Vec::new();
        for a in problem.instvars.iter() {
            let ssigma: Sigma = a.iter().map(|i| eval_term_partial(*i, &problem.constraint.elems, &bsigma).unwrap()).collect();
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

fn add_node(node: Node, ctxt: &mut Ctxt) -> (usize, Option<Id>) {
    let Some(vals) = vals(&node, ctxt) else { return (0, None) };
    let count_sat;

    if let Some(&i) = ctxt.vals_lookup.get(&vals) {
        let newsize = minsize(&node, ctxt);
        let c = &mut ctxt.classes[i];
        if newsize < c.size {
            c.size = newsize;
            c.node = node.clone();
            enqueue(i, ctxt);
        }
        count_sat = ctxt.classes[i].satcount;
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

        count_sat = satcount;

        // dbg!(extract(i, ctxt));

        // if this [Value] was successful, return it.
        if satcount == ctxt.big_sigmas.len() {
            return (count_sat, Some(i));
        }

        enqueue(i, ctxt);
    }

    (count_sat, None)
}

// From my understanding this is equivalent to A* search
fn enqueue(x: Id, ctxt: &mut Ctxt) {
    let h = heuristic_bayes(x, ctxt);
    println!("this: {}", h);
    ctxt.queue.push(WithOrd(x, h));
}

// In this paper they also use satcount as a reward to a reinforcement learner
//   -> Put here for purpose of referencing if we want
//   -> https://www.cs.toronto.edu/~six/data/iclr19.pdf
#[allow(unused)]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    if let Ty::Bool = c.node.ty() {
        return OrderedFloat(1000f64);
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

    OrderedFloat((a / (c.size + 5)) as f64)
}

#[allow(unused)]
fn heuristic_perceptron(x: Id, ctxt: &Ctxt) -> Score {
    todo!();
}

#[allow(unused)]
fn heuristic_bayes(x: Id, ctxt: &Ctxt) -> Score {
    todo!();
}

// TODO: Include an embedding of the program
// From Machine Learning for Automated Theorem Proving: Learning to Solve SAT and QSAT:
//   => Can us a GNN to encode formula as a vector (X needs pretraining and overkill)
//   => R feature: ratio of clasues to number of variables of the problem
//   => Formula as binary strings representing if a literal appeared in a clause
//   => For a CNF: Clause-variable incidence graph
//                 Variable incidence graph
//                 Clause incidence graph
//   => 12 groups of the _standard features_
//   => Structure related features
// Can utilise information from the previous iteration
//   => What clause gave the new counterexample
//   => Why did it not solve the spec
//   => etc.
fn get_features(x: Id, ctxt: &Ctxt) -> Vec<f64> {
    let c = &ctxt.classes[x];

    let subterms = c.node.children();
    let mut subterm_satcount: Vec<f64> = subterms
        .iter()
        .map(|s| ctxt.classes[*s].satcount as f64)
        .collect();
    subterm_satcount.resize(3, 0f64);

    let mut X = vec![c.satcount as f64, c.size as f64];
    X.extend_from_slice(&subterm_satcount);
    let ty = match c.node.ty() {
        Ty::Int => 1f64,
        Ty::Bool => 0f64,
    };
    X.push(ty);
    X
}

fn vals(node: &Node, ctxt: &Ctxt) -> Option<Box<[Value]>> {
    ctxt.small_sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |id: Id| Some(ctxt.classes[id].vals[i].clone());
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

    eval_term(&ctxt.problem.constraint, &huge_sigma).unwrap() == Value::Bool(true)
}

fn extract(x: Id, ctxt: &Ctxt) -> Term {
    let mut t = Term { elems: Vec::new() };
    let f = &|c: Id| ctxt.classes[c].node.clone();
    ctxt.classes[x].node.extract(f, &mut t.elems);
    t
}
