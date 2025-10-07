use crate::*;

use indexmap::IndexSet;
use itertools::Itertools;
use std::collections::{HashSet, HashMap};
use std::collections::hash_map::Entry;
use ordered_float::OrderedFloat;


type Score = OrderedFloat<f32>;
type Queue = BinaryHeap<WithOrd<(usize, Id), Score>>;
type NodeQueue = BinaryHeap<WithOrd<Node, usize>>;
type NonTerminal = usize;

pub struct Seen(HashMap<(NonTerminal, Id), HashSet<Id>>);
impl Seen {
    pub fn new() -> Self {
        Seen(HashMap::new())
    }

    pub fn contains_or_insert(&mut self, nt: NonTerminal, id: Id) -> bool {
        match self.0.entry((nt, id)) {
            Entry::Vacant(e) => {
                e.insert(HashSet::from([id]));
                true
            }
            Entry::Occupied(_) => false,
        }
    }
}

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

pub struct Class {
    node: Node,
    nodes: NodeQueue,
    size: usize,
    vals: Box<[Value]>,
    handled_size: Option<usize>, // what was the size when this class was handled last time.
    satcount: usize,
    prev_sol: usize,
    features: Vec<f32>
}

fn run(ctxt: &mut Ctxt) -> Term {

    if cfg!(feature = "simple_incremental") {
        let mut seen = Seen::new();
        for nt in 0..ctxt.classes.len() {
            for id in 0..ctxt.classes[nt].len() {
                if seen.contains_or_insert(nt, id) {
                    if let Some((nt, _sol)) = add_class_part(nt, id, ctxt, &mut seen) {
                        handle_sol(nt, _sol, ctxt);
                        return extract(nt, _sol, ctxt);
                    }
                }
            }
        }
    }

    if cfg!(feature = "winning_incremental") {
        let mut seen = Seen::new();
        for nt in 0..ctxt.classes.len() {
            'cs: for id in 0..ctxt.classes[nt].len() {
                if ctxt.classes[nt][id].prev_sol > 0  && seen.contains_or_insert(nt, id) {
                    if let Some((nt, _sol)) = add_class_part(nt, id, ctxt, &mut seen) {
                        handle_sol(nt, _sol, ctxt);
                        return extract(nt, _sol, ctxt);
                    }
                } 
            }
        }
    }

    for (nt, n) in ctxt.problem.prod_rules() {
        let n = n.clone();
        if n.children().is_empty() {
            let (_sol, is_sol, maxsat) = add_node(*nt, n, ctxt, None);
            if is_sol {
                handle_sol(*nt, _sol, ctxt);
                return extract(*nt, _sol, ctxt);
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

                let (_sol, is_sol, sc) = add_node(out_type, rule.clone(), ctxt, None);
                if is_sol {
                    return (Some((out_type, _sol)), maxsat);
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
        classes: classes.unwrap_or_else(|| {
            std::iter::repeat_with(|| Vec::<Class>::new())
                .take(no_nt)
                .collect::<Vec<Vec<Class>>>()
        }),
        solids: vec![vec![]; no_nt],
        perceptron,
    };

    (run(&mut ctxt), ctxt.cxs_cache, ctxt.classes)
}


fn add_class_part(nt: NonTerminal, id: Id, ctxt: &mut Ctxt, seen: &mut Seen) -> Option<(NonTerminal, Id)> {
    add_canon_node_part(nt, id, ctxt, seen);
    let vals = ctxt.classes[nt][id].vals.to_vec();
    let new_sigmas = ctxt.classes[nt][id].vals.len();
    let class = &mut ctxt.classes[nt][id];
    let heap = std::mem::take(&mut class.nodes);

    for WithOrd(n, _) in heap.into_sorted_vec().into_iter().skip(1) {
        if let Some(id) = add_nodes_part(nt, id, n, ctxt, seen, &vals, new_sigmas) {
            return Some((nt, id));
        }
    }

    None
}

fn add_nodes_part(nt: NonTerminal, id: Id, node: Node, ctxt: &mut Ctxt, seen: &mut Seen, vals: &[Value], ns: usize) -> Option<Id> {
    for (cnt, c) in node.signature().0.iter().zip(node.children()) {
        if let (Ty::NonTerminal(j), Child::Hole(i)) = (cnt, c) {
            if seen.contains_or_insert(*j, *i) {
                add_class_part(*j, *i, ctxt, seen);
            }
       }
    }


    println!("\n{:?}", node);
    for comb in node.signature().0.iter().zip(node.children())
        .map(|(cnt, c)| {
            if let (Ty::NonTerminal(j), Child::Hole(i)) = (cnt, c) {
                seen.0[&(*j, *i)].clone().into_iter().collect::<Vec<_>>()
            } else { vec![0] } // dummy id 
        })
        .multi_cartesian_product() 
    {
        let mut new_node = node.clone();
        for (idx, c) in new_node.children_mut().iter_mut().enumerate() {
            match c {
                Child::Hole(i) => *c = Child::Hole(comb[idx]),
                _ => { } 
            }
        }
        println!("\n {:?}, {:?}", comb,  new_node);
        let (idx, sol, sc) = add_node_part(nt, id, new_node, ctxt, seen, vals, ns);
        if sol { 
            return Some(idx)
        }
    }

    None

}

fn add_node_part(nt: NonTerminal, id: Id, node: Node, ctxt: &mut Ctxt, seen: &mut Seen, vals: &[Value], ns: usize) -> (Id, bool, usize) {
    let mut delta = Vec::new();
    for (i, sigma) in ctxt.small_sigmas[ns..].iter().enumerate() {
        let f = |cnt: NonTerminal, id: Id| Some(ctxt.classes[cnt][id].vals[ns + i].clone());
        delta.push(node.eval(&f, sigma).expect("eval failed"));
    }

    let mut full_vals = vals.clone().to_vec();
    full_vals.extend(delta);

    let (nid, sol, sc) = add_node(nt, node, ctxt, Some(full_vals.clone().into_boxed_slice()));
    seen.0.get_mut(&(nt, id)).unwrap().insert(nid); 

    (nid, sol, sc)
}


fn add_canon_node_part(nt: NonTerminal, id: Id, ctxt: &mut Ctxt, seen: &mut Seen) {
    let node = ctxt.classes[nt][id].node.clone();
    let ns = ctxt.classes[nt][id].vals.len();

    for (cnt, c) in node.signature().0.iter().zip(node.children()) {
        if let (Ty::NonTerminal(j), Child::Hole(i)) = (cnt, c) {
            if seen.contains_or_insert(*j, *i) {
                add_class_part(*j, *i, ctxt, seen);
            }
       }
    }

    let mut delta = Vec::new();
    for (i, sigma) in ctxt.small_sigmas[ns..].iter().enumerate() {
        let f = |cnt: NonTerminal, idx: Id| Some(ctxt.classes[cnt][idx].vals[ns + i].clone());
        delta.push(node.eval(&f, sigma).expect("eval failed"));
    }

    let mut full_vals = ctxt.classes[nt][id].vals.clone().to_vec();
    full_vals.extend(delta);

    let full_boxed: Box<[Value]> = full_vals.into_boxed_slice();
    ctxt.classes[nt][id].vals = full_boxed.clone();

    ctxt.vals_lookup.insert((nt, full_boxed), id);

    ctxt.solids[nt].push(id); 

    if ctxt.problem.rettys.contains(&ctxt.classes[nt][id].node.ty()) {
        ctxt.classes[nt][id].satcount += satcount(nt, id, ctxt, Some(vec![ctxt.big_sigmas.len() - 1]));
    }

    enqueue(nt, id, ctxt);
}


fn add_node(nt: NonTerminal, node: Node, ctxt: &mut Ctxt, provided_vals: Option<Box<[Value]>>) -> (Id, bool, usize) {
    let vals = match provided_vals {
        Some(v) => v,
        None => match vals(nt, &node, ctxt) {
            Some(v) => v,
            None => return (0, false, 0), //is this okay? i dunno for now
        },
    };
    let sc;
    let i;

    if let Some(&j) = ctxt.vals_lookup.get(&(nt, vals.clone())) {
        let newsize = minsize(nt, &node, ctxt);
        let c = &mut ctxt.classes[nt][j];
        sc = c.satcount;
        if newsize < c.size {
            c.size = newsize;
            c.node = node.clone();
            c.node = node.clone();
            enqueue(nt, j, ctxt);
        } 
        ctxt.classes[nt][j].nodes.push(WithOrd(node, newsize));
        i = j
    } else {
        i = ctxt.classes[nt].len();
        let size = minsize(nt, &node, ctxt);
        let mut nodes = NodeQueue::with_capacity(4);
        nodes.push(WithOrd(node.clone(), size));
        let c = Class {
            size,
            node,
            nodes,
            vals: vals.clone(),
            handled_size: None,
            satcount: 0, // will be set later!
            prev_sol: 0,
            features: Vec::new(),
        };
        ctxt.classes[nt].push(c);

        if ctxt.big_sigmas.len() > 0 {
            let mut satc= 0;
            let mut to_check = Vec::new();
            for (i , chunk) in ctxt.sigma_indices.iter().enumerate() {
                let vals_chunk = chunk.iter().map(|idx| vals[*idx].clone()).collect::<Vec<_>>();
                if let Some(b) = ctxt.cxs_cache[i].get::<[core::Value]>(&vals_chunk) {
                    satc += *b as usize;
                } else {
                    to_check.push(i);
                }
            }


            if !to_check.is_empty() {
                satc += satcount(nt, i, ctxt, Some(to_check));
            };
            sc = satc;

            ctxt.classes[nt][i].satcount = sc;
        } else {
            sc = 0
        }

        // dbg!(extract(i, ctxt));

        ctxt.vals_lookup.insert((nt, vals), i);

        if sc == ctxt.big_sigmas.len() && ctxt.problem.rettys.contains(&Ty::NonTerminal(nt)) { // ugly but ok
            return (i, true, sc);
        }

        enqueue(nt, i, ctxt);
    }

    (i, false, sc)
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
