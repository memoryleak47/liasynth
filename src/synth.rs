use crate::*;

use itertools::Itertools;
use std::collections::HashSet;
use ordered_float::OrderedFloat;

type Score = OrderedFloat<f32>;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

// SmallSigma has as many values as our synthfun has arguments.
// BigSigma has as many values as our Sygus file declares.
// HugeSigma is BigSigma extended by one variable per instantiation of the synthfun.

pub struct Ctxt<'a> {
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

    perceptron: &'a Perceptron, // persistent learner through whole task
}

#[derive(Clone)]
pub struct Class {
    node: Node,
    size: usize,
    vals: Box<[Value]>,
    handled_size: Option<usize>, // what was the size when this class was handled last time.
    satcount: usize,
    prev_sol: usize,
    features: Vec<f32>
}

fn run(ctxt: &mut Ctxt) -> Term {

    let mut seen: HashSet<usize> = HashSet::new();
    for id in 0..ctxt.classes.len() {
        if seen.get(&id).is_none() {
            add_node_part(id, ctxt, &mut seen);
        }
    }

    for n in ctxt.problem.prod_rules() {
        let n = n.clone();
        if n.children().is_empty() {
            let (_sol, maxsat) = add_node(n, ctxt);
            if let Some(sol) = _sol {
                handle_sol(sol, ctxt);
                return extract(sol, ctxt);
            }
            ctxt.perceptron.train(ctxt.classes[n.ident].features, maxsat);
        }
    }

    while let Some(WithOrd(x, _)) = ctxt.queue.pop() {
        let (_sol, maxsat) = handle(x, ctxt);
        if let Some(sol) = _sol {
            handle_sol(sol, ctxt);
            return extract(sol, ctxt);
        }
    }

    panic!("No term found!")
}

fn handle_sol(id: Id, ctxt: &mut Ctxt) {
    ctxt.classes[id].prev_sol += 1;
    let node = ctxt.classes[id].node.clone();
    for c in node.children() {
        handle_sol(*c, ctxt);
    }
}

// makes "x" solid if it's not solid yet.
fn handle(x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let c = &mut ctxt.classes[x];

    // if the current size is the same size of the last "handle" call, nothing it to be done.
    if c.handled_size == Some(c.size) { return (None, 0); }

    if c.handled_size.is_none() {
        match c.node.ty() {
            Ty::Int => &mut ctxt.i_solids,
            Ty::Bool => &mut ctxt.b_solids,
        }.push(x);
    }

    c.handled_size = Some(c.size);

    grow(x, ctxt)
}

fn grow(x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let ty = ctxt.classes[x].node.ty();
    let mut maxsat = 0;

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

                let (_sol, sc) = add_node(rule.clone(), ctxt);
                if let Some(sol) = _sol {
                    return (Some(sol), maxsat);
                }
                maxsat = std::cmp::max(maxsat, sc);
            }
        }
    }

    (None, maxsat)
}

pub fn synth(problem: &Problem, big_sigmas: &[Sigma], classes: Option<Vec<Class>>, perceptron: &Perceptron) -> (Term, Vec<Class>) {
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

    let mut ctxt = Ctxt {
        queue: Default::default(),
        big_sigmas,
        small_sigmas,
        sigma_indices,
        problem,
        vals_lookup: Default::default(),
        classes: classes.unwrap_or(Vec::new()),
        i_solids: Vec::new(),
        b_solids: Vec::new(),
        perceptron,
    };

    (run(&mut ctxt), ctxt.classes)
}


fn add_node_part(id: Id, ctxt: &mut Ctxt, seen: &mut HashSet<usize>) {
    let node = ctxt.classes[id].node.clone();
    let new_sigmas = ctxt.classes[id].vals.len();

    for c in node.children() {
       if seen.get(&id).is_none() {
          add_node_part(*c, ctxt, seen);
       }
    }

    let new_vals: Vec<Value> = {
        let mut vals = Vec::new();
        for (i, sigma) in ctxt.small_sigmas[new_sigmas..].iter().enumerate() {
            let f = |id: Id| {
                Some(ctxt.classes[id].vals[new_sigmas + i].clone())
            } ;
            match node.eval(&f, sigma) {
                Some(val) => vals.push(val),
                None => panic!("Why cannot evaluate?")
            }
        }
        vals
    };

    let mut temp_vec = ctxt.classes[id].vals.clone().into_vec();
    temp_vec.extend(new_vals);
    ctxt.classes[id].vals = temp_vec.into_boxed_slice();

    ctxt.vals_lookup.insert(ctxt.classes[id].vals.clone(), id);

    let bs = ctxt.big_sigmas.len() - 1;
    ctxt.classes[id].satcount += if ctxt.classes[id].node.ty() != ctxt.problem.rettype {
        0
    } else {
        local_sat(bs, id, ctxt) as usize
    };

    seen.insert(id);

    enqueue(id, ctxt);
}


fn add_node(node: Node, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let Some(vals) = vals(&node, ctxt) else { return (None, 0) };
    let sc;

    if let Some(&i) = ctxt.vals_lookup.get(&vals) {
        let newsize = minsize(&node, ctxt);
        let c = &mut ctxt.classes[i];
        sc = c.satcount;
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
            prev_sol: 0,
        });
        ctxt.vals_lookup.insert(vals, i);

        let satcount = satcount(i, ctxt);
        ctxt.classes[i].satcount = satcount;
        sc = satcount;

        // dbg!(extract(i, ctxt));

        // if this [Value] was successful, return it.
        if satcount == ctxt.big_sigmas.len() {
            return (Some(i), sc);
        }

        enqueue(i, ctxt);
    }

    (None, sc)
}

fn enqueue(x: Id, ctxt: &mut Ctxt) {
    let h = heuristic(x, ctxt);
    ctxt.queue.push(WithOrd(x, h));
}

#[cfg(feature = "heuristic_default")]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    if let Ty::Bool = c.node.ty() {
        return OrderedFloat(10000 as f32);
    }

    let mut a = 100000;
    let subterms = c.node.children();
    let max_subterm_satcount = subterms
        .iter()
        .map(|s| ctxt.classes[*s].satcount)
        .max()
        .unwrap_or_else(|| 0);


    let tmp = c.satcount.saturating_sub(max_subterm_satcount + 4);

    for _ in tmp..ctxt.big_sigmas.len() {
        a /= 2;
    }

    for _ in 0..c.prev_sol+1 {
        a/=2;
    }

    OrderedFloat((a / (c.size + 5)) as f32)
}

#[cfg(feature = "heurisitc_perceptron")]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let feats = feature_set1(x, ctxt);
    let score = ctxt.perceptron.predict(feats);

    OrderedFloat(score)
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
