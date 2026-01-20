use crate::*;

use hashbrown::DefaultHashBuilder;
use indexmap::IndexSet;
use itertools::Itertools;
use ordered_float::OrderedFloat;
use priority_queue::PriorityQueue;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

type Score = OrderedFloat<f64>;
type Queue = PriorityQueue<(usize, Id), Score, DefaultHashBuilder>;
type NodeQueue = BinaryHeap<WithOrd<Node, usize>>;

#[cfg(all(feature = "simple", any(feature = "winning")))]
compile_error!("simple is incompatible with winning");

const WINNING: bool = cfg!(feature = "winning");
const MAXSIZE: usize = if cfg!(feature = "total") { 100 } else { 0 };
// TODO: find a better way to only do incremental on certain nodes/for certain programs

fn push_bounded<T: Ord>(heap: &mut BinaryHeap<T>, val: T) {
    heap.push(val);
    if heap.len() > MAXSIZE {
        heap.pop();
    }
}

fn insert_if_absent<K, V>(map: &mut HashMap<K, V>, key: K) -> bool
where
    K: std::hash::Hash + Eq,
    V: Default,
{
    match map.entry(key) {
        Entry::Vacant(e) => {
            e.insert(V::default());
            true
        }
        Entry::Occupied(_) => false,
    }
}

pub struct Ctxt<'a> {
    pub queue: Queue, // contains ids of pending (i.e. not solidifed Ids), or solid Ids which got an updated size.

    pub big_sigmas: &'a [Sigma],
    pub small_sigmas: Box<[Sigma]>,

    // for each big_sigma, thisreturns the list of small_sigmas corresponding to the instantiations of the synthfun.
    pub sigma_indices: Box<[Box<[usize]>]>,

    pub problem: &'a Problem,

    // indexed by small-sigma.
    pub vals_lookup: Map<(usize, Box<[Value]>), Id>,
    pub cxs_cache: Vec<HashMap<Box<[Value]>, bool>>,

    pub classes: Vec<Class>,

    pub solids: Vec<Vec<Id>>,

    pub temb: &'a mut TermEmbedder,
    pub olinr: &'a mut BayesianLinearRegression,
    pub seen_scs: Vec<HashSet<u64>>,
}

pub struct Class {
    pub node: Node,
    pub nodes: NodeQueue,
    pub complex: usize,
    pub vals: Box<[Value]>,
    pub handled_complex: Option<usize>, // what was the size when this class was handled last time.
    pub satcount: u64,
    pub prev_sol: usize,
    pub in_sol: bool,
    pub features: Vec<f64>,
}

impl Class {
    fn default_class(complex: usize, node: Node, vals: Box<[Value]>) -> Self {
        Class {
            complex,
            node: node.clone(),
            nodes: NodeQueue::from([WithOrd(node, complex)]),
            vals: vals.clone(),
            handled_complex: None,
            satcount: 0,
            prev_sol: 0,
            in_sol: false,
            features: Vec::new(),
        }
    }
}

pub fn synth(
    problem: &Problem,
    big_sigmas: &[Sigma],
    cxs_cache: Option<Vec<HashMap<Box<[Value]>, bool>>>,
    classes: Option<Vec<Class>>,
    temb: &mut TermEmbedder,
    olinr: &mut BayesianLinearRegression,
) -> (Term, Vec<HashMap<Box<[Value]>, bool>>, Vec<Class>) {
    let mut small_sigmas: IndexSet<Sigma> = IndexSet::new();
    let mut sigma_indices: Vec<Box<[usize]>> = Vec::new();
    for bsigma in big_sigmas {
        let mut indices = Vec::new();
        for a in &problem.instvars {
            let ssigma: Sigma = a
                .iter()
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
        classes: classes.unwrap_or(Vec::new()),
        temb,
        solids: vec![vec![]; no_nt],
        olinr,
        seen_scs: vec![HashSet::new(); no_nt],
    };

    (run(&mut ctxt), ctxt.cxs_cache, ctxt.classes)
}

fn run(ctxt: &mut Ctxt) -> Term {
    // time_block!("synth.run");

    // ctxt.olinr.on_curriculum_change(0.0, 1.00);

    if cfg!(any(feature = "simple", feature = "winning",)) {
        if let Some(solution) = incremental_comp(ctxt) {
            return solution;
        }
    } else {
        ctxt.classes.drain(..);
    };

    let _solution = enumerate_atoms(ctxt)
        .or_else(|| enumerate(ctxt))
        .map(|solution| solution);

    if let Some(solution) = _solution {
        return solution;
    } else {
        panic!("infeasible")
    }
}

fn incremental_comp(ctxt: &mut Ctxt) -> Option<Term> {
    let mut seen: HashMap<Id, Vec<Id>> = HashMap::new();

    for id in 0..ctxt.classes.len() {
        if (!WINNING || (ctxt.classes[id].prev_sol > 0 || ctxt.classes[id].in_sol))
            && insert_if_absent(&mut seen, id)
        {
            if let Some(id) = incremental_add_class(id, &mut seen, ctxt) {
                handle_solution(id, ctxt);
                return Some(extract(id, ctxt));
            }
        }
    }
    None
}

fn incremental_add_class(id: Id, seen: &mut HashMap<Id, Vec<Id>>, ctxt: &mut Ctxt) -> Option<Id> {
    let vals = ctxt.classes[id].vals.to_vec();
    let nt = ctxt.classes[id].node.ty().into_nt().unwrap();

    if let Some(id) = update_class(nt, id, &vals, seen, ctxt) {
        return Some(id);
    }
    None
}

fn update_children(node: &Node, seen: &mut HashMap<Id, Vec<Id>>, ctxt: &mut Ctxt) {
    let rc = node
        .children()
        .iter()
        .filter_map(|n| {
            if let Child::Hole(_, i) = n {
                Some(*i)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    for c in rc {
        if insert_if_absent(seen, c) {
            incremental_add_class(c, seen, ctxt);
        }
    }
}

// We cannot support cycles hence sometimes return an Err
fn update_vals(node: &Node, vals: &Vec<Value>, ctxt: &Ctxt) -> Result<Box<[Value]>, ()> {
    let mut new_vals: Vec<Value> = vals.clone();
    for (i, sigma) in ctxt.small_sigmas[vals.len()..].iter().enumerate() {
        let f = |idx: Id| {
            ctxt.classes
                .get(idx)
                .and_then(|class| class.vals.get(vals.len() + i))
                .cloned()
        };
        let res = node.eval(&f, sigma).ok_or(())?;
        new_vals.push(res);
    }
    Ok(new_vals.into_boxed_slice())
}

fn update_class(
    nt: usize,
    id: Id,
    vals: &Vec<Value>,
    seen: &mut HashMap<Id, Vec<Id>>,
    ctxt: &mut Ctxt,
) -> Option<Id> {
    let nodes = std::mem::take(&mut ctxt.classes[id].nodes);
    let node = ctxt.classes[id].node.clone();
    update_children(&node, seen, ctxt);

    let Ok(new_vals) = update_vals(&node, vals, ctxt) else {
        return None;
    };
    ctxt.classes[id].vals = new_vals.clone();
    ctxt.vals_lookup.insert((nt, new_vals), id);

    seen.get_mut(&id).unwrap().push(id);
    let new_sat = satcount(nt, id, ctxt, Some(vec![ctxt.big_sigmas.len() - 1]));
    if new_sat != 0 {
        ctxt.classes[id].satcount |= new_sat;
        // ctxt.seen_scs[nt].insert(ctxt.classes[id].satcount.clone());
        seen_insert_maximal(&mut ctxt.seen_scs[nt], ctxt.classes[id].satcount);
    }
    enqueue(nt, id, ctxt);

    if ctxt.classes[id].prev_sol > 0 {
        for WithOrd(n, _) in nodes.into_sorted_vec().into_iter().skip(1) {
            if let Some(id) = add_incremental_nodes(id, nt, n, vals, seen, ctxt) {
                return Some(id);
            }
        }
    }

    None
}

fn add_incremental_nodes(
    oid: Id,
    nt: usize,
    node: Node,
    vals: &Vec<Value>,
    seen: &mut HashMap<Id, Vec<Id>>,
    ctxt: &mut Ctxt,
) -> Option<Id> {
    update_children(&node, seen, ctxt);

    let child_ids: Vec<(usize, Vec<Id>)> = node
        .children()
        .iter()
        .enumerate()
        .filter_map(|(pos, c)| {
            if let Child::Hole(_, i) = c {
                let ids: Vec<Id> = seen.get(i).cloned().unwrap_or_default();
                Some((pos, ids))
            } else {
                None
            }
        })
        .collect();

    for combination in child_ids
        .iter()
        .map(|(pos, ids)| ids.iter().map(move |id| (*pos, *id)))
        .multi_cartesian_product()
    {
        let mut new_node = node.clone();
        for (pos, c_idx) in &combination {
            let ty_nt = node.signature().0[*pos].into_nt().unwrap();
            new_node.children_mut()[*pos] = Child::Hole(ty_nt, *c_idx);
        }

        let Ok(new_vals) = update_vals(&new_node, vals, ctxt) else {
            return None;
        };

        if !ctxt.vals_lookup.contains_key(&(nt, new_vals.clone())) {
            let (id, is_sol, satcount) = add_node(nt, new_node, ctxt, Some(new_vals));
            // ctxt.seen_scs[nt].insert(satcount.clone());
            seen_insert_maximal(&mut ctxt.seen_scs[nt], satcount);
            seen.get_mut(&oid).unwrap().push(id);
            ctxt.classes[id].prev_sol = ctxt.classes[oid].prev_sol;
            ctxt.classes[id].satcount = satcount;
            if is_sol {
                return Some(id);
            }
            ctxt.classes[id].handled_complex = Some(ctxt.classes[id].complex);
            // for o in ctxt.problem.nt_tc.reached_by(nt) {
            //     ctxt.solids[*o].push(id);
            // }
        }
    }
    None
}

fn enumerate_atoms(ctxt: &mut Ctxt) -> Option<Term> {
    for (nt, n) in ctxt.problem.prod_rules() {
        let is_ph = matches!(n, Node::PlaceHolder(_, _));
        let holed = n.children().iter().any(|c| matches!(c, Child::Hole(_, _)));

        if (n.children().is_empty() || !holed) && !is_ph {
            let (id, is_sol, _) = add_node(*nt, n.clone(), ctxt, None);
            if is_sol {
                handle_solution(id, ctxt);
                return Some(extract(id, ctxt));
            }
            ctxt.problem.nt_tc.reached_by(*nt).iter().for_each(|o| {
                ctxt.solids[*o].push(id);
            });
            ctxt.classes[id].handled_complex = Some(ctxt.classes[id].complex);
        }
    }

    None
}

fn enumerate(ctxt: &mut Ctxt) -> Option<Term> {
    while let Some(((nt, x), _)) = ctxt.queue.pop() {
        let (id, maxsat) = handle(nt, x, ctxt);
        if let Some(solution) = id {
            handle_solution(solution, ctxt);
            return Some(extract(solution, ctxt));
        }

        if cfg!(feature = "learned") {
            let num_cxs = ctxt.big_sigmas.len();
            let normalised_score = if num_cxs > 0 {
                maxsat as f64 / num_cxs as f64
            } else {
                0.0
            };

            ctxt.olinr
                .update(ctxt.classes[x].features.as_slice(), normalised_score);
        }
    }
    None
}

fn handle_solution(id: Id, ctxt: &mut Ctxt) {
    ctxt.classes[id].prev_sol = ctxt.big_sigmas.len();
    let children = ctxt.classes[id]
        .node
        .children()
        .iter()
        .filter_map(|c| match c {
            Child::Hole(_, i) => Some(*i),
            _ => None,
        })
        .collect::<Vec<_>>();

    for c_id in children {
        handle_sub_solution(c_id, ctxt);
    }
}

fn handle_sub_solution(id: Id, ctxt: &mut Ctxt) {
    ctxt.classes[id].in_sol = true;
    let children = ctxt.classes[id]
        .node
        .children()
        .iter()
        .filter_map(|c| match c {
            Child::Hole(_, i) => Some(*i),
            _ => None,
        })
        .collect::<Vec<_>>();

    for c_id in children {
        handle_sub_solution(c_id, ctxt);
    }
}

fn handle(nt: usize, x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let c = &mut ctxt.classes[x];
    for o in ctxt.problem.nt_tc.reached_by(nt) {
        ctxt.solids[*o].push(x);
    }

    c.handled_complex = Some(c.complex);
    grow(nt, x, ctxt)
}

type Sat = u64;

#[inline(always)]
fn is_subset(a: Sat, b: Sat) -> bool {
    (a & b) == a
}

fn seen_insert_maximal(seen: &mut HashSet<Sat>, new: Sat) {
    if seen.iter().any(|&sc| is_subset(new, sc)) {
        return;
    }

    seen.retain(|&sc| !is_subset(sc, new));
    seen.insert(new);
}

#[inline(always)]
fn dominated_by_superset(sat: Sat, seen: &HashSet<Sat>) -> bool {
    seen.iter().any(|&sc| is_subset(sat, sc) && sc != sat)
}

fn prune(nt: usize, rule: &Node, children: &[(usize, Id)], ctxt: &Ctxt) -> bool {
    let rt = &rule.signature().1.into_nt().unwrap();
    let seen = &ctxt.seen_scs[nt];

    match rule.template() {
        Some("(ite ? ? ?)") => {
            let [(_, cond), (tt, b_then), (te, b_else)] = children else {
                return false;
            };

            if ctxt.classes[*cond].node.template() == Some("(not ?)") {
                if let Some(Child::Hole(_, c)) = ctxt.classes[*cond].node.children().first() {
                    if ctxt.classes[*c].node.signature().1 == ctxt.classes[*cond].node.signature().1
                    {
                        return true;
                    }
                }
            }

            if b_then == b_else && tt == te {
                return true;
            }

            let cond_vals = &ctxt.classes[*cond].vals;
            if cond_vals.len() > 1 && cond_vals.iter().all_equal() && rt == tt && rt == te {
                return true;
            }

            let then_sc = ctxt.classes[*b_then].satcount;
            if dominated_by_superset(then_sc, seen) {
                return true;
            }

            let else_sc = ctxt.classes[*b_else].satcount;
            if dominated_by_superset(else_sc, seen) {
                return true;
            }

            return (rt == tt && ctxt.classes[*b_then].satcount == 0)
                || (rt == te && ctxt.classes[*b_else].satcount == 0);
        }

        Some("(div ? ?)") | Some("(mod ? ?)") => {
            if let [(at, a), (_bt, b)] = children {
                match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                    (_, Node::ConstInt(0, _) | Node::ConstInt(1, _)) => {
                        return nt == *at;
                    }
                    _ => {}
                }

                let b_vals = &ctxt.classes[*b].vals;
                return (rt == at)
                    && (b_vals.iter().all(|v| *v == Value::Int(0))
                        || b_vals.iter().all(|v| *v == Value::Int(1)));
            }
        }
        Some("(+ ? ?)") => {
            if let [(at, a), (bt, b)] = children {
                if a > b && at == bt {
                    return true;
                }

                match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                    (_, Node::ConstInt(0, _)) => {
                        return nt == *at;
                    }
                    (Node::ConstInt(0, _), _) => {
                        return nt == *bt;
                    }
                    _ => {}
                }

                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;
                return !a_vals.is_empty()
                    && (rt == at && a_vals.iter().all(|v| *v == Value::Int(0)))
                    || (rt == bt && b_vals.iter().all(|v| *v == Value::Int(0)));
            }
        }

        Some("(- ? ?)") => {
            if let [(at, _a), (_bt, b)] = children {
                let b_vals = &ctxt.classes[*b].vals;
                return (rt == at) && b_vals.iter().all(|v| *v == Value::Int(0));
            }
        }

        Some("(* ? ?)") => {
            if let [(at, a), (bt, b)] = children {
                if a > b && at == bt {
                    return true;
                }

                match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                    (_, Node::ConstInt(0, _) | Node::ConstInt(1, _)) => {
                        return *at == nt;
                    }
                    (Node::ConstInt(0, _) | Node::ConstInt(1, _), _) => {
                        return nt == *bt;
                    }
                    _ => {}
                }

                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;
                return (rt == at
                    && (a_vals.iter().all(|v| *v == Value::Int(0))
                        || a_vals.iter().all(|v| *v == Value::Int(1))))
                    || (rt == bt
                        && (b_vals.iter().all(|v| *v == Value::Int(0))
                            || b_vals.iter().all(|v| *v == Value::Int(1))));
            }
        }
        Some("(and ? ?)") | Some("(or ? ?)") => {
            if let [(at, a), (bt, b)] = children {
                if a > b && at == bt {
                    return true;
                }

                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;

                if !a_vals.len() <= 1 && a_vals.iter().all_equal() && b_vals.iter().all_equal() {
                    return true;
                }

                if !a_vals.is_empty() {
                    if a_vals.iter().zip(b_vals.iter()).all(|(i, j)| match (i, j) {
                        (Value::Bool(x), Value::Bool(y)) => x == &(!*y),
                        _ => false,
                    }) {
                        return true;
                    }
                }
            }
        }

        Some("(> ? ?)") | Some("(>= ? ?)") | Some("(< ? ?)") | Some("(<= ? ?)") => {
            if let [(at, a), (bt, b)] = children {
                if a == b && at == bt && !ctxt.classes[*a].vals.len() <= 1 {
                    return true;
                }

                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;
                if !a_vals.len() <= 1 {
                    if a_vals.iter().all_equal() && b_vals.iter().all_equal() {
                        return true;
                    }
                }
            }
        }
        Some("(= ? ?)") | Some("(xor ? ?)") | Some("(distinct ? ?)") => {
            if let [(at, a), (bt, b)] = children {
                if a > b && at == bt {
                    return true;
                }
                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;
                if !a_vals.len() <= 1 {
                    if a_vals.iter().all_equal() && b_vals.iter().all_equal() {
                        return true;
                    }
                }
            }
        }
        _ => {}
    }

    match rule.signature() {
        (_, Ty::Bool) if rule.children().len() > 1 => children.iter().all_equal(),
        _ => false,
    }
}

fn grow(nt: usize, x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let mut max_sat = 0;
    let nt_reached = ctxt.problem.nt_tc.reached_by(nt).clone();

    for (pnt, rule) in ctxt.problem.prod_rules() {
        let (in_types, _) = rule.signature();

        let mut nt_by_pos = vec![usize::MAX; in_types.len()];
        for (pos, ty) in in_types.iter().enumerate() {
            if matches!(ty, Ty::PRule(_)) {
                nt_by_pos[pos] = ty.into_nt().unwrap();
            }
        }

        'rule: for (i, child) in rule.children().iter().enumerate() {
            if !matches!(child, Child::Hole(_, _)) {
                continue;
            }

            let child_nt = in_types[i].into_nt().unwrap();
            if !nt_reached.contains(&child_nt) {
                continue;
            }

            let mut base_prog = rule.clone();
            base_prog.children_mut()[i] = Child::Hole(child_nt, x);

            let remaining_children_nts: Vec<(usize, &Ty)> = in_types
                .iter()
                .enumerate()
                .filter(|(idx, _)| *idx != i)
                .collect();

            let rel_children: Vec<(usize, Vec<Id>)> = remaining_children_nts
                .iter()
                .filter(|(_, ty)| matches!(ty, Ty::PRule(_)))
                .map(|(pos, ty)| {
                    let ids = match ty {
                        Ty::PRule(_) => ctxt
                            .problem
                            .nt_tc
                            .reached_by(ty.into_nt().unwrap())
                            .iter()
                            .flat_map(|o| ctxt.solids[*o].clone())
                            .collect::<Vec<Id>>(),
                        _ => vec![],
                    };
                    (*pos, ids)
                })
                .collect();

            if rel_children.is_empty() || rel_children.iter().any(|(_, ids)| ids.is_empty()) {
                if remaining_children_nts
                    .iter()
                    .all(|(_, ty)| !matches!(ty, Ty::PRule(_)))
                {
                    let (id, is_sol, satcount) = add_node(*pnt, base_prog, ctxt, None);
                    max_sat = max_sat.max(satcount.count_ones());
                    if is_sol {
                        return (Some(id), max_sat as usize);
                    }
                }
                continue 'rule;
            }

            let base_children = base_prog.children().to_vec();

            let hole_pos: Vec<usize> = rule
                .children()
                .iter()
                .enumerate()
                .filter_map(|(p, ch)| matches!(ch, Child::Hole(_, _)).then_some(p))
                .collect();

            let mut by_pos: Vec<(usize, Id)> = vec![(usize::MAX, 0); in_types.len()];
            let mut child_ids: Vec<(usize, Id)> = Vec::with_capacity(hole_pos.len());

            for combination in rel_children
                .iter()
                .map(|(pos, ids)| ids.iter().map(move |id| (*pos, *id)))
                .multi_cartesian_product()
            {
                by_pos[i] = (child_nt, x);
                for (pos, id) in &combination {
                    by_pos[*pos] = (nt_by_pos[*pos], *id);
                }

                child_ids.clear();
                child_ids.extend(hole_pos.iter().map(|&p| by_pos[p]));

                if prune(nt, rule, &child_ids, ctxt) {
                    continue;
                }

                let mut prog = base_prog.clone();
                prog.children_mut().copy_from_slice(&base_children);
                for (pos, c_idx) in &combination {
                    let nt2 = nt_by_pos[*pos];
                    prog.children_mut()[*pos] = Child::Hole(nt2, *c_idx);
                }

                let (id, is_sol, satcount) = add_node(*pnt, prog.clone(), ctxt, None);

                max_sat = max_sat.max(satcount.count_ones());
                if is_sol {
                    return (Some(id), max_sat as usize);
                }
            }
        }
    }

    (None, max_sat as usize)
}

fn enqueue(nt: usize, x: Id, ctxt: &mut Ctxt) {
    let h = heuristic(x, ctxt);
    ctxt.queue.push((nt, x), h);
}

fn add_node(nt: usize, node: Node, ctxt: &mut Ctxt, vals: Option<Box<[Value]>>) -> (Id, bool, u64) {
    let vals = vals.unwrap_or_else(|| match gen_vals(&node, ctxt) {
        Some(v) => v,
        _ => panic!("Could not generate vals"),
    });

    // GLOBAL_STATS.lock().unwrap().programs_generated += 1;

    let (id, satcount) = if let Some(&_id) = ctxt.vals_lookup.get(&(nt, vals.clone())) {
        let newcomplex = mincomplexity(&node, ctxt);
        let c = &mut ctxt.classes[_id];
        let _satcount = c.satcount;
        if newcomplex < c.complex {
            c.complex = newcomplex;
            c.node = node.clone();
            if c.handled_complex.is_none() {
                enqueue(nt, _id, ctxt);
            }
        }
        if cfg!(feature = "total") {
            push_bounded(&mut ctxt.classes[_id].nodes, WithOrd(node, newcomplex));
        }
        (_id, _satcount)
    } else {
        // GLOBAL_STATS.lock().unwrap().new_programs_generated += 1;
        let _id = ctxt.classes.len();
        let complexity = mincomplexity(&node, ctxt);
        let c = Class::default_class(complexity, node, vals.clone());

        ctxt.classes.push(c);

        let mut _satcount = 0;
        let mut to_check = Vec::new();
        for (i, chunk) in ctxt.sigma_indices.iter().enumerate() {
            let vals_chunk = chunk
                .iter()
                .map(|idx| vals[*idx].clone())
                .collect::<Vec<_>>();
            if let Some(b) = ctxt.cxs_cache[i].get::<[core::Value]>(&vals_chunk) {
                if *b {
                    _satcount |= 1 << i;
                }
            } else {
                to_check.push(i);
            }
        }

        if !to_check.is_empty() {
            let sc = satcount(nt, _id, ctxt, Some(to_check));
            _satcount |= sc;
        }

        seen_insert_maximal(&mut ctxt.seen_scs[nt], _satcount);
        let sc = _satcount.count_ones();
        ctxt.classes[_id].satcount = _satcount;
        ctxt.vals_lookup.insert((nt, vals), _id);

        if (ctxt.sigma_indices.len() == sc as usize)
            && ctxt.problem.rettys.contains(&Ty::NonTerminal(nt))
        {
            return (_id, true, _satcount);
        }

        enqueue(nt, _id, ctxt);

        (_id, _satcount)
    };

    (id, false, satcount)
}

fn gen_vals(node: &Node, ctxt: &Ctxt) -> Option<Box<[Value]>> {
    let mut out = Vec::with_capacity(ctxt.small_sigmas.len());

    for (sigma_idx, sigma) in ctxt.small_sigmas.iter().enumerate() {
        out.push(node.eval_idx(ctxt, sigma_idx, sigma)?);
    }

    Some(out.into_boxed_slice())
}

fn mincomplexity(node: &Node, ctxt: &Ctxt) -> usize {
    node.children()
        .iter()
        .filter_map(|x| {
            if let Child::Hole(_, i) = x {
                Some(i)
            } else {
                None
            }
        })
        .map(|x| ctxt.classes[*x].complex)
        .sum::<usize>()
        + 1
}

pub fn extract(x: Id, ctxt: &Ctxt) -> Term {
    let mut t = Term { elems: Vec::new() };
    let f = &|c: Id| ctxt.classes[c].node.clone();
    ctxt.classes[x].node.extract(f, &mut t.elems);
    t
}

#[cfg(all(feature = "rf", feature = "expert"))]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    let ty = ctxt.classes[x].node.ty();
    let l = ctxt.big_sigmas.len() as f64;
    let normaliser = c.complex as f64;

    if ctxt
        .problem
        .nt_mapping
        .get(&ty)
        .expect("this never happens")
        != &ctxt.problem.rettype
    {
        let half = l / 0.3;
        let score = 2.0 - (-2.0 * (1.0 * half) / (l * l)).exp();
        return OrderedFloat(score / normaliser);
    }

    let (add_value, lost_value) = c
        .node
        .children()
        .iter()
        .filter_map(|ch| match ch {
            Child::Hole(_, i) => Some(*i),
            _ => None,
        })
        .fold((0.0f64, 0.0f64), |(add, lost), s| {
            let sc = ctxt.classes[s].satcount;
            (
                add + (c.satcount & !sc).count_ones() as f64,
                lost + (!c.satcount & sc).count_ones() as f64,
            )
        });

    let sc = c.satcount.count_ones() as f64;
    let score = 3.3 - (-2.8 * (sc * (add_value - lost_value)) / (l * l)).exp();

    OrderedFloat(score / normaliser)
}

#[cfg(all(feature = "lia", feature = "expert"))]
fn heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    let ty = ctxt.classes[x].node.ty();
    let l = ctxt.big_sigmas.len() as f64;
    let normaliser = c.complex as f64;

    if ctxt
        .problem
        .nt_mapping
        .get(&ty)
        .expect("this never happens")
        != &ctxt.problem.rettype
    {
        let half = l / 1.6;
        let score = 1.0 - (-2.0 * (1.0 * half) / (l * l)).exp();
        return OrderedFloat(score / normaliser);
    }
    let max_subterm_satcount = c
        .node
        .children()
        .iter()
        .filter_map(|ch| match ch {
            Child::Hole(_, i) => Some(*i),
            _ => None,
        })
        .map(|s| ctxt.classes[*s].satcount.count_ones())
        .max()
        .unwrap_or_else(|| 0);

    let sc = c.satcount.count_ones();
    let diff = sc.saturating_sub(max_subterm_satcount) as f64;
    let score = 1.0 - (-2.0 * (diff * sc as f64) / (l * l)).exp();

    OrderedFloat(score / normaliser)
}

fn expm1_norm(x: f64, l: f64, alpha: f64) -> f64 {
    if l <= 0.0 {
        return 0.5;
    }
    if x <= 0.0 {
        return 0.0;
    }

    let ratio = x / l;
    let z = (alpha * ratio).exp_m1();
    let n = alpha.exp_m1();

    let result = z / n;
    result.clamp(0.0, 1.0)
}

#[cfg(feature = "learned")]
fn feature_set(x: Id, ctxt: &mut Ctxt) -> Vec<f64> {
    let c = &ctxt.classes[x];
    let term = extract(x, ctxt);
    let w2v: Vec<f64> = ctxt.temb.embed(&term);
    let l = ctxt.big_sigmas.len() as f64;

    let sc = c.satcount.count_ones() as f64;
    let max_subterm_satcount = c
        .node
        .children()
        .iter()
        .filter_map(|c| {
            if let Child::Hole(_, i) = c {
                Some(i)
            } else {
                None
            }
        })
        .map(|s| ctxt.classes[*s].satcount.count_ones())
        .max()
        .unwrap_or(0) as f64;

    let diff = f64::max(sc - max_subterm_satcount, 0.0);

    vec![
        expm1_norm(sc, l, 1.7),
        expm1_norm(diff, l, 3.5),
        (1.0 / c.complex as f64).exp(),
    ]
    .into_iter()
    .chain(w2v)
    .collect()
}

#[cfg(feature = "learned")]
fn heuristic(x: Id, ctxt: &mut Ctxt) -> Score {
    let ty = ctxt.classes[x].node.ty();
    let mut feats = feature_set(x, ctxt);
    let (log_odds, _) = ctxt.olinr.predict(feats.as_slice());
    let score = log_odds.clamp(-10.0, 10.0).exp() / ctxt.classes[x].complex as f64;

    ctxt.classes[x].features = feats;
    OrderedFloat(score)
}

#[cfg(feature = "random")]
fn heuristic(_x: Id, _ctxt: &mut Ctxt) -> Score {
    OrderedFloat(rand::random::<f64>())
}

#[cfg(feature = "size")]
fn heuristic(x: Id, ctxt: &mut Ctxt) -> Score {
    OrderedFloat(1.0 / ctxt.classes[x].complex as f64)
}
