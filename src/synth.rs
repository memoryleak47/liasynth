use crate::*;

use indexmap::IndexSet;
use itertools::Itertools;
use std::collections::{HashSet, HashMap};
use ordered_float::OrderedFloat;

type Score = OrderedFloat<f32>;
type Queue = BinaryHeap<WithOrd<(usize, Id), Score>>;
type NonTerminal = usize;

// SmallSigma has as many values as our synthfun has arguments.
// BigSigma has as many values as our Sygus file declares.
// HugeSigma is BigSigma extended by one variable per instantiation of the synthfun.

pub struct Ctxt<'a> {
    queue: Queue, // contains ids of pending (i.e. not solidifed Ids), or solid Ids which got an updated size.

    big_sigmas: &'a [Sigma],
    small_sigmas: Box<[Sigma]>,

    // for each big_sigma, thisreturns the list of small_sigmas corresponding to the instantiations of the synthfun.
    sigma_indices: Box<[Box<[usize]>]>,

    problem: &'a Problem,

    // indexed by small-sigma.
    vals_lookup: Map<(NonTerminal, Box<[Value]>), Id>,
    cxs_cache: Vec<HashMap<Box<[Value]>, bool>>,

    classes: Vec<Vec<Class>>,

    solids: Vec<Vec<Id>>,

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

    if cfg!(feature = "simple_incremental") {
        let mut seen: HashSet<(NonTerminal, Id)> = HashSet::new();
        for nt in 0..ctxt.classes.len() {
            for id in 0..ctxt.classes[nt].len() {
                if seen.insert((nt, id)) {
                    add_node_part(nt, id, ctxt, &mut seen);
                }
            }
        }
    }

    if cfg!(feature = "winning_incremental") {
        let mut seen: HashSet<(NonTerminal, Id)> = HashSet::new();
        for nt in 0..ctxt.classes.len() {
            'cs: for id in 0..ctxt.classes[nt].len() {
                if ctxt.classes[nt][id].prev_sol > 0 && seen.get(&(nt, id)).is_none() {
                    add_node_part(nt, id, ctxt, &mut seen);
                } 
            }
        }
    }

    for (nt, n) in ctxt.problem.prod_rules() {
        let n = n.clone();
        if n.children().is_empty() {
            let (_sol, maxsat) = add_node(*nt, n, ctxt);
            if let Some(sol) = _sol {
                handle_sol(*nt, sol, ctxt);
                return extract(*nt, sol, ctxt);
            }
            // ctxt.perceptron.train(ctxt.classes[n.ident].features, maxsat);
        }
    }

    while let Some(WithOrd((nt, x), _)) = ctxt.queue.pop() {
        let (_sol, maxsat) = handle(nt, x, ctxt);
        if let Some((ot, sol)) = _sol {
            handle_sol(ot, sol, ctxt);
            return extract(ot, sol, ctxt);
        }
        // ctxt.perceptron.train(ctxt.classes[n.ident].features, maxsat);
    }

    panic!("infeasible")
}

fn handle_sol(nt: NonTerminal, id: Id, ctxt: &mut Ctxt) {
    ctxt.classes[nt][id].prev_sol += 1;
    let node = ctxt.classes[nt][id].node.clone();
    for (arg_ty, child) in node.signature().0.iter().zip(node.children()) {
        if let (Ty::NonTerminal(j), Child::Hole(i)) = (arg_ty, child) {
            handle_sol(*j, *i, ctxt);
        }
    }
}

// makes "x" solid if it's not solid yet.
fn handle(nt: NonTerminal, x: Id, ctxt: &mut Ctxt) -> (Option<(usize, Id)>, usize) {
    let c = &mut ctxt.classes[nt][x];

    // if the current size is the same size of the last "handle" call, nothing it to be done.
    if c.handled_size == Some(c.size) { return (None, 0); }

    if c.handled_size.is_none() {
        ctxt.solids[nt].push(x);
    }

    c.handled_size = Some(c.size);

    grow(nt, x, ctxt)
}

fn grow(nt: usize, x: Id, ctxt: &mut Ctxt) -> (Option<(usize, Id)>, usize) {
    let ty = ctxt.classes[nt][x].node.ty();
    let mut maxsat = 0;

    for (nt, rule) in ctxt.problem.prod_rules() {
        let (in_types, Ty::NonTerminal(out_type)) = rule.signature() else { panic!("what is happening: rule: {:?}  sig: {:?}", rule, rule.signature()) };
        for i in 0..rule.children().len() {
            if matches!(rule.children()[i], Child::VarInt(_) | Child::VarBool(_) | Child::Constant(_)) || rule.children()[i] != Child::Hole(0) {
                continue;
            }
            let mut rule = rule.clone();
            if in_types[i] != ty { continue }
            rule.children_mut()[i] = Child::Hole(x);

            let mut in_types: Vec<_> = in_types.iter().cloned().collect();
            in_types.remove(i);
            let it = in_types.iter().map(|ty| match ty {
                Ty::NonTerminal(i) => ctxt.solids[*i].clone().into_iter(),
                _ => panic!("should not happen"),
            });

            for a in it.multi_cartesian_product() {
                rule.children_mut().iter_mut().enumerate()
                    .filter(|(_, c)| matches!(c, Child::Hole(_)))
                    .filter(|(i2, _)| *i2 != i)
                    .map(|(_, x)| x)
                    .zip(a.iter()).for_each(|(ptr, v)| { *ptr = Child::Hole(*v); });

                let (_sol, sc) = add_node(out_type, rule.clone(), ctxt);
                if let Some(sol) = _sol {
                    return (Some((out_type, sol)), maxsat);
                }
                maxsat = std::cmp::max(maxsat, sc);
            }
        }
    }

    (None, maxsat)
}

pub fn synth(problem: &Problem, big_sigmas: &[Sigma], cxs_cache: Option<Vec<HashMap<Box<[Value]>, bool>>>, classes: Option<Vec<Vec<Class>>>, perceptron: &Perceptron) -> (Term, Vec<HashMap<Box<[Value]>, bool>>, Vec<Vec<Class>>) {
    let mut small_sigmas: IndexSet<Sigma> = IndexSet::new();
    let mut sigma_indices: Vec<Box<[usize]>> = Vec::new();
    for bsigma in big_sigmas {
        let mut indices = Vec::new();
        for a in &problem.instvars {
            let ssigma: Sigma = a.iter()
                .map(|i| eval_term_partial(*i, &problem.constraint.elems, bsigma).unwrap())
                .collect();

            let (idx, _) = small_sigmas.insert_full(ssigma);
            indices.push(idx);
        }
        sigma_indices.push(indices.into_boxed_slice());
    }
    let small_sigmas: Box<[Sigma]> = small_sigmas.into_iter().collect();
    let sigma_indices: Box<[Box<[usize]>]> = sigma_indices.into();
    let no_nt = problem.synth_fun.nonterminal_defs.len();

    let mut cxs_cache = cxs_cache.unwrap_or(Vec::new());
    cxs_cache.push(HashMap::new());

    let mut ctxt = Ctxt {
        queue: Default::default(),
        big_sigmas,
        small_sigmas,
        sigma_indices,
        problem,
        vals_lookup: Default::default(),
        cxs_cache, 
        classes: classes.unwrap_or(vec![vec![]; no_nt]),
        solids: vec![vec![]; no_nt],
        perceptron,
    };

    (run(&mut ctxt), ctxt.cxs_cache, ctxt.classes)
}


fn add_node_part(nt: NonTerminal, id: Id, ctxt: &mut Ctxt, seen: &mut HashSet<(NonTerminal, Id)>) {
    let node = ctxt.classes[nt][id].node.clone();
    let new_sigmas = ctxt.classes[nt][id].vals.len();

    for (cnt, c) in node.signature().0.iter().zip(node.children()) {
        if let (Ty::NonTerminal(j), Child::Hole(i)) = (cnt, c) {
            if seen.insert((*j, *i)) {
                add_node_part(*j, *i, ctxt, seen);
            }
       }
    }

    let new_vals: Vec<Value> = {
        let mut vals = Vec::new();
        for (i, sigma) in ctxt.small_sigmas[new_sigmas..].iter().enumerate() {
            let f = |cnt: NonTerminal, id: Id| {
                Some(ctxt.classes[cnt][id].vals[new_sigmas + i].clone())
            } ;
            match node.eval(&f, sigma) {
                Some(val) => vals.push(val),
                None => panic!("Why cannot evaluate?")
            }
        }
        vals
    };

    ctxt.solids[nt].push(id); 

    let mut vals = ctxt.classes[nt][id].vals.clone().into_vec(); 
    vals.extend(new_vals);
    let vals_boxed: Box<[Value]> = vals.into_boxed_slice();
    ctxt.classes[nt][id].vals = vals_boxed.clone();

    ctxt.vals_lookup.insert((nt, vals_boxed), id);

    if ctxt.problem.rettys.contains(&ctxt.classes[nt][id].node.ty()) {
        ctxt.classes[nt][id].satcount += satcount(nt, id, ctxt, Some(vec![ctxt.big_sigmas.len() - 1]));
    }

    enqueue(nt, id, ctxt);
}


fn add_node(nt: NonTerminal, node: Node, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let Some(vals) = vals(nt, &node, ctxt) else { return (None, 0) };
    let sc;

    if let Some(&i) = ctxt.vals_lookup.get(&(nt, vals.clone())) {
        let newsize = minsize(nt, &node, ctxt);
        let c = &mut ctxt.classes[nt][i];
        sc = c.satcount;
        if newsize < c.size {
            c.size = newsize;
            c.node = node.clone();
            enqueue(nt, i, ctxt);
        }
    } else {
        let i = ctxt.classes[nt].len();
        let c = Class {
            size: minsize(nt, &node, ctxt),
            node,
            vals: vals.clone(),
            handled_size: None,
            satcount: 0, // will be set later!
            prev_sol: 0,
            features: Vec::new(),
        };
        ctxt.classes[nt].push(c);

        if ctxt.big_sigmas.len() > 0 {
            let no_vals = ctxt.small_sigmas.len() / ctxt.big_sigmas.len();

            let mut satc= 0;
            let mut to_check = Vec::new();
            for (i , chunk) in vals.chunks_exact(no_vals).enumerate() {
                if let Some(b) = ctxt.cxs_cache[i].get::<[core::Value]>(chunk) {
                    satc += *b as usize;
                } else {
                    to_check.push(i);
                }
            }

            let idxs = if to_check.is_empty() {
                None
            } else { Some(to_check) };

            satc += satcount(nt, i, ctxt, idxs);
            sc = satc;

            ctxt.classes[nt][i].satcount = sc;
        } else {
            sc = 0
        }

        // dbg!(extract(i, ctxt));

        ctxt.vals_lookup.insert((nt, vals), i);

        if sc == ctxt.big_sigmas.len() && ctxt.problem.rettys.contains(&Ty::NonTerminal(nt)) { // ugly but ok
            return (Some(i), sc);
        }

        enqueue(nt, i, ctxt);
    }

    (None, sc)
}

fn enqueue(nt: NonTerminal, x: Id, ctxt: &mut Ctxt) {
    let h = heuristic(nt, x, ctxt);
    ctxt.queue.push(WithOrd((nt, x), h));
}

#[cfg(feature = "heuristic_default")]
fn heuristic(nt: NonTerminal, x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[nt][x];
    if nt != 0 {
        return OrderedFloat(10000 as f32);
    }

    let mut a = 100000;
    let subterms = c.node.signature().0.iter().zip(c.node.children());
    let max_subterm_satcount = subterms
        .filter_map(|(cnt, s)| {
            if let Child::Hole(i) = s && let Ty::NonTerminal(j) = cnt { Some((j, i)) } else { None }
        })
        .map(|(cnt, s)| ctxt.classes[*cnt][*s].satcount)
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

#[cfg(feature = "heuristic_perceptron")]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let feats = feature_set1(x, ctxt);
    let score = ctxt.perceptron.predict(feats);

    OrderedFloat(score)
}

fn vals(nt: NonTerminal, node: &Node, ctxt: &Ctxt) -> Option<Box<[Value]>> {
    ctxt.small_sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |cnt: NonTerminal, id: Id| Some(ctxt.classes[cnt][id].vals[i].clone());
        node.eval(&f, sigma)
    }).collect()
}

fn minsize(nt: NonTerminal, node: &Node, ctxt: &Ctxt) -> usize {
    node.signature().0.iter().zip(node.children())
        .filter_map(|(cnt, x)| if let Child::Hole(i) = x && let Ty::NonTerminal(j) = cnt { Some((j, i)) } else { None })
        .map(|(cnt, x)| ctxt.classes[*cnt][*x].size).sum::<usize>() + 1
}

fn satcount(nt: NonTerminal, x: Id, ctxt: &mut Ctxt, idxs: Option<Vec<usize>>) -> usize {
    let ty = ctxt.classes[nt][x].node.ty();
    if ctxt.problem.nt_mapping.get(&ty).expect("this never happens") != &ctxt.problem.rettype {
        return 0;
    }
    let t = extract(nt, x, ctxt);
    let no_vals = ctxt.small_sigmas.len() / ctxt.big_sigmas.len();

    if let Some(idxs) = idxs {
        let r = ctxt.problem.satisfy(&t, idxs.iter().map(|&i| ctxt.big_sigmas[i].as_slice()));
        for (pos, &i) in idxs.iter().enumerate() {
            let start = i * no_vals;
            let vchunk = &ctxt.classes[nt][x].vals[start .. start + no_vals];
            ctxt.cxs_cache[i].insert(Box::<[Value]>::from(vchunk), r[pos]);
        }
        return r.iter().map(|x| *x as usize).sum();
    }

    let r = ctxt.problem.satisfy(&t, ctxt.big_sigmas.iter().map(|v| v.as_slice()));
    for (i, (vchunk, &res)) in ctxt.classes[nt][x]
        .vals
        .chunks_exact(no_vals)
        .zip(r.iter())
        .enumerate()
    {
        ctxt.cxs_cache[i].insert(Box::<[Value]>::from(vchunk), res);
    }
    r.iter().map(|x| *x as usize).sum()
}

fn extract(nt: NonTerminal, x: Id, ctxt: &Ctxt) -> Term {
    let mut t = Term { elems: Vec::new() };
    let f = &|cnt: NonTerminal, c: Id| ctxt.classes[cnt][c].node.clone();
    ctxt.classes[nt][x].node.extract(f, &mut t.elems);
    t
}
