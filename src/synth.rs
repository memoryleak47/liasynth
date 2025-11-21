use crate::*;

use indexmap::IndexSet;
use itertools::Itertools;
use ordered_float::OrderedFloat;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

type Score = OrderedFloat<f64>;
type Queue = BinaryHeap<WithOrd<(usize, Id), Score>>;
type NodeQueue = BinaryHeap<WithOrd<Node, usize>>;

#[cfg(all(feature = "simple", any(feature = "winning")))]
compile_error!("simple is incompatible with winning");

const WINNING: bool = cfg!(feature = "winning");
const MAXSIZE: usize = if cfg!(feature = "total") { 6 } else { 0 };
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
    pub flinr: &'a mut BayesianLinearRegression,
}

pub struct Class {
    pub node: Node,
    pub nodes: NodeQueue,
    pub size: usize,
    pub vals: Box<[Value]>,
    pub handled_size: Option<usize>, // what was the size when this class was handled last time.
    pub satcount: usize,
    pub prev_sol: usize,
    pub in_sol: bool,
    pub features: Vec<f64>,
}

impl Class {
    fn default_class(size: usize, node: Node, vals: Box<[Value]>) -> Self {
        Class {
            size,
            node: node.clone(),
            nodes: NodeQueue::from([WithOrd(node, size)]),
            vals: vals.clone(),
            handled_size: None,
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
    flinr: &mut BayesianLinearRegression,
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
        flinr,
    };

    (run(&mut ctxt), ctxt.cxs_cache, ctxt.classes)
}

fn run(ctxt: &mut Ctxt) -> Term {
    time_block!("synth.run");

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
        if insert_if_absent(&mut seen, id)
            && (!WINNING || (ctxt.classes[id].prev_sol > 0 || ctxt.classes[id].in_sol))
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

// TODO: We have an issue with cycles hence needing to return an Err
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
    for o in ctxt.problem.nt_tc.reached_by(nt) {
        ctxt.solids[*o].push(id);
    }

    ctxt.classes[id].satcount += satcount(nt, id, ctxt, Some(vec![ctxt.big_sigmas.len() - 1]));
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

        let Ok(new_vals) = update_vals(&node, vals, ctxt) else {
            return None;
        };
        let (id, is_sol, satcount) = add_node(nt, new_node, ctxt, Some(new_vals));
        ctxt.classes[id].prev_sol = ctxt.classes[oid].prev_sol;

        if is_sol {
            return Some(id);
        }

        if satcount > ctxt.classes[oid].satcount {
            seen.get_mut(&oid).unwrap().push(id);
            for o in ctxt.problem.nt_tc.reached_by(nt) {
                ctxt.solids[*o].push(id);
            }

            enqueue(nt, id, ctxt);
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
            ctxt.classes[id].handled_size = Some(0);
        }
    }

    None
}

fn enumerate(ctxt: &mut Ctxt) -> Option<Term> {
    while let Some(WithOrd((nt, x), _s)) = ctxt.queue.pop() {
        let (id, maxsat) = handle(nt, x, ctxt);
        if let Some(solution) = id {
            handle_solution(solution, ctxt);
            return Some(extract(solution, ctxt));
        }

        if cfg!(feature = "learned") {
            let target = if ctxt.problem.nt_mapping[&Ty::NonTerminal(nt)] == ctxt.problem.rettype {
                &mut ctxt.olinr
            } else {
                &mut ctxt.flinr
            };

            target.update(ctxt.classes[x].features.as_slice(), maxsat as f64);
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
    if c.handled_size == Some(c.size) {
        return (None, 0);
    }

    if c.handled_size.is_none() {
        for o in ctxt.problem.nt_tc.reached_by(nt) {
            ctxt.solids[*o].push(x);
        }
    }

    c.handled_size = Some(c.size);
    grow(nt, x, ctxt)
}

fn prune(nt: usize, rule: &Node, children: &[Id], ctxt: &Ctxt) -> bool {
    match rule.ident() {
        "Ite" => {
            let [cond, b_then, b_else] = children else {
                unreachable!()
            };
            if b_then > b_else {
                return true;
            }

            let cond_vals = &ctxt.classes[*cond].vals;
            if cond_vals.len() > 1 && cond_vals.iter().all(|v| *v == cond_vals[0]) {
                return true;
            }

            ctxt.classes[*b_then].satcount == 0 || ctxt.classes[*b_else].satcount == 0
        }
        _ if children.len() == 2
            && matches!(
                rule.ident(),
                "Add" | "Mul" | "Equals" | "And" | "Xor" | "Distinct" | "Or"
            ) =>
        {
            children[0] == children[1]
        }
        "Add" => {
            if let [a, b] = children {
                match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                    (_, Node::ConstInt(0, ty)) | (Node::ConstInt(0, ty), _) => {
                        return nt == ty.into_nt().unwrap();
                    }
                    _ => {}
                }
                return ctxt.classes[*a].vals.iter().all(|v| *v == Value::Int(0))
                    || ctxt.classes[*b].vals.iter().all(|v| *v == Value::Int(0));
            }
            false
        }
        "Mul" => {
            if let [a, b] = children {
                match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                    (_, Node::ConstInt(0, ty) | Node::ConstInt(1, ty))
                    | (Node::ConstInt(0, ty) | Node::ConstInt(1, ty), _) => {
                        return nt == ty.into_nt().unwrap();
                    }
                    _ => {}
                }
                let a_vals = &ctxt.classes[*a].vals;
                let b_vals = &ctxt.classes[*b].vals;
                return a_vals.iter().all(|v| *v == Value::Int(0))
                    || a_vals.iter().all(|v| *v == Value::Int(1))
                    || b_vals.iter().all(|v| *v == Value::Int(0))
                    || b_vals.iter().all(|v| *v == Value::Int(1));
            }
            false
        }
        _ => match rule.signature() {
            (_, Ty::Bool) if rule.children().len() > 1 => {
                children.iter().all(|c| *c == children[0])
            }
            _ => false,
        },
    }
}

fn grow(nt: usize, x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let mut max_sat = 0;
    let nt_reached = ctxt.problem.nt_tc.reached_by(nt).clone();

    for (pnt, rule) in ctxt.problem.prod_rules() {
        let (in_types, _) = rule.signature();

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
                    max_sat = max_sat.max(satcount);
                    if is_sol {
                        return (Some(id), max_sat);
                    }
                }
                continue 'rule;
            }

            for combination in rel_children
                .iter()
                .map(|(pos, ids)| ids.iter().map(move |id| (*pos, *id)))
                .multi_cartesian_product()
            {
                let mut new_children = combination.clone();
                new_children.push((i, x));
                let child_ids: Vec<usize> = new_children.iter().map(|(_, c)| *c).collect();

                if !prune(nt, rule, &child_ids, ctxt) {
                    let mut prog = base_prog.clone();
                    for (pos, c_idx) in &combination {
                        let ty_nt = in_types[*pos].into_nt().unwrap();
                        prog.children_mut()[*pos] = Child::Hole(ty_nt, *c_idx);
                    }

                    let (id, is_sol, satcount) = add_node(*pnt, prog.clone(), ctxt, None);

                    // let t = extract(id, ctxt);
                    // println!(
                    //     "{:?}",
                    //     term_to_z3(&t, &ctxt.problem.vars.keys().cloned().collect::<Box<[_]>>())
                    // );

                    max_sat = max_sat.max(satcount);
                    if is_sol {
                        return (Some(id), max_sat);
                    }
                }
            }
        }
    }

    (None, max_sat)
}

fn enqueue(nt: usize, x: Id, ctxt: &mut Ctxt) {
    let h = if cfg!(feature = "learned") {
        learned_heuristic(x, ctxt)
    } else {
        default_heuristic(x, ctxt)
    };

    ctxt.queue.push(WithOrd((nt, x), h));
}

fn add_node(
    nt: usize,
    node: Node,
    ctxt: &mut Ctxt,
    vals: Option<Box<[Value]>>,
) -> (Id, bool, usize) {
    let vals = vals.unwrap_or_else(|| match gen_vals(&node, ctxt) {
        Some(v) => v,
        _ => panic!("Could not generate vals"),
    });

    GLOBAL_STATS.lock().unwrap().programs_generated += 1;

    let (id, satcount) = if let Some(&_id) = ctxt.vals_lookup.get(&(nt, vals.clone())) {
        let newsize = minsize(&node, ctxt);
        let c = &mut ctxt.classes[_id];
        let _satcount = c.satcount;
        if newsize < c.size {
            c.size = newsize;
            c.node = node.clone();
            enqueue(nt, _id, ctxt);
        }
        push_bounded(&mut ctxt.classes[_id].nodes, WithOrd(node, newsize));
        (_id, _satcount)
    } else {
        GLOBAL_STATS.lock().unwrap().new_programs_generated += 1;

        let _id = ctxt.classes.len();
        let size = minsize(&node, ctxt);
        let c = Class::default_class(size, node, vals.clone());

        ctxt.classes.push(c);

        let mut _satcount = 0;
        let mut to_check = Vec::new();
        for (i, chunk) in ctxt.sigma_indices.iter().enumerate() {
            let vals_chunk = chunk
                .iter()
                .map(|idx| vals[*idx].clone())
                .collect::<Vec<_>>();
            if let Some(b) = ctxt.cxs_cache[i].get::<[core::Value]>(&vals_chunk) {
                _satcount += *b as usize;
            } else {
                to_check.push(i);
            }
        }
        if !to_check.is_empty() {
            _satcount += satcount(nt, _id, ctxt, Some(to_check));
        };

        ctxt.classes[_id].satcount = _satcount;
        ctxt.vals_lookup.insert((nt, vals), _id);

        if _satcount == ctxt.big_sigmas.len() && ctxt.problem.rettys.contains(&Ty::NonTerminal(nt))
        {
            return (_id, true, _satcount);
        }

        enqueue(nt, _id, ctxt);

        (_id, _satcount)
    };

    (id, false, satcount)
}

fn gen_vals(node: &Node, ctxt: &Ctxt) -> Option<Box<[Value]>> {
    ctxt.small_sigmas
        .iter()
        .enumerate()
        .map(|(i, sigma)| {
            let f = |id: Id| Some(ctxt.classes[id].vals[i].clone());
            node.eval(&f, sigma)
        })
        .collect()
}

fn minsize(node: &Node, ctxt: &Ctxt) -> usize {
    node.children()
        .iter()
        .filter_map(|x| {
            if let Child::Hole(_, i) = x {
                Some(i)
            } else {
                None
            }
        })
        .map(|x| ctxt.classes[*x].size)
        .sum::<usize>()
        + 1
}

pub fn extract(x: Id, ctxt: &Ctxt) -> Term {
    let mut t = Term { elems: Vec::new() };
    let f = &|c: Id| ctxt.classes[c].node.clone();
    ctxt.classes[x].node.extract(f, &mut t.elems);
    t
}

fn default_heuristic(x: Id, ctxt: &Ctxt) -> Score {
    let c = &ctxt.classes[x];
    let ty = ctxt.classes[x].node.ty();
    let l = ctxt.big_sigmas.len() as f64;
    let normaliser = (c.size) as f64;

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
        .filter_map(|c| {
            if let Child::Hole(_, i) = c {
                Some(i)
            } else {
                None
            }
        })
        .map(|s| ctxt.classes[*s].satcount)
        .max()
        .unwrap_or_else(|| 0);

    let diff = c.satcount.saturating_sub(max_subterm_satcount) as f64;
    let score = 1.0 - (-2.0 * (diff * c.satcount as f64) / (l * l)).exp();

    OrderedFloat(score / normaliser)
}

fn feature_set(x: Id, ctxt: &mut Ctxt) -> Vec<f64> {
    let c = &ctxt.classes[x];
    let term = extract(x, ctxt);

    let w2v: Vec<f64> = ctxt.temb.embed(&term);

    let sc = c.satcount;
    let mut iter = c.node.children().iter().filter_map(|c| match c {
        Child::Hole(_, i) => Some(ctxt.classes[*i].satcount),
        _ => None,
    });

    let (min_subterm_sc, max_subterm_sc) = if let Some(first) = iter.next() {
        iter.fold((first, first), |(min, max), ssc| {
            (min.min(ssc), max.max(ssc))
        })
    } else {
        (0, 0)
    };

    vec![
        1.0,
        c.prev_sol as f64,
        max_subterm_sc as f64,
        min_subterm_sc as f64,
        sc as f64,
    ]
    .into_iter()
    .chain(w2v)
    .collect()
}

fn learned_heuristic(x: Id, ctxt: &mut Ctxt) -> Score {
    let ty = ctxt.classes[x].node.ty();
    let ret = &ctxt.problem.rettype;
    let is_off = ctxt
        .problem
        .nt_mapping
        .get(&ty)
        .map(|t| t != ret)
        .unwrap_or(true);

    let mut feats = feature_set(x, ctxt);

    let score = if is_off {
        feats[3] = (ctxt.big_sigmas.len() as f64) / 2.0;
        let (s, _) = ctxt.flinr.predict(feats.as_slice());
        s
    } else {
        let (s, _) = ctxt.olinr.predict(feats.as_slice());
        s
    };
    ctxt.classes[x].features = feats;

    let thresh = if matches!(ret, Ty::Int) {
        45_000
    } else {
        15_000
    };
    if GLOBAL_STATS.lock().unwrap().programs_generated < thresh {
        default_heuristic(x, ctxt)
    } else {
        OrderedFloat(score / ((ctxt.classes[x].size + 5) as f64))
    }
}
