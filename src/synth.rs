use crate::*;

use indexmap::IndexSet;
use itertools::Itertools;
use ordered_float::OrderedFloat;
use rand::Rng;
use rand::seq::IndexedRandom;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};

type Score = OrderedFloat<f64>;
type Queue = BinaryHeap<WithOrd<(usize, Id), Score>>;
type NodeQueue = BinaryHeap<WithOrd<Node, usize>>;

#[cfg(all(feature = "simple", any(feature = "winning")))]
compile_error!("simple is incompatible with winning");

const WINNING: bool = cfg!(feature = "winning");
const MAXSIZE: usize = if cfg!(feature = "total") { 5 } else { 0 };

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
    pub vals_lookup: Map<(NonTerminal, Box<[Value]>), Id>,
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

    enumerate_atoms(ctxt)
        .or_else(|| enumerate(ctxt))
        .map(|solution| return solution);

    panic!("infeasible")
}

fn incremental_comp(ctxt: &mut Ctxt) -> Option<Term> {
    let mut seen: HashMap<Id, Vec<Id>> = HashMap::new();
    let c_and_idx = ctxt.classes.iter().enumerate();

    for (id, c) in c_and_idx {
        if insert_if_absent(&mut seen, id) && (WINNING && (c.prev_sol > 0 || c.in_sol)) {
            todo!();
        }
    }

    None
}

fn enumerate_atoms(ctxt: &mut Ctxt) -> Option<Term> {
    for (nt, n) in ctxt.problem.prod_rules() {
        let is_ph = matches!(n, Node::PlaceHolder(_, _));
        let holed = n.children().iter().any(|c| matches!(c, Child::Hole(_, _)));

        if (n.children().is_empty() || !holed) && !is_ph {
            let (id, is_sol, satcount) = add_node(n.clone(), ctxt, None);
            if is_sol {
                handle_solution(id, ctxt);
                return extract(id, ctxt);
            }
            ctxt.problem.nt_tc.reached_by(*nt).iter().for_each(|pnt| {
                ctxt.solids[*nt].push(id);
            });
            ctxt.classes[id].handled_size = Some(0);
        }
    }
    None
}

fn enumerate(ctxt: &mut Ctxt) -> Option<Term> {
    while let Some(WithOrd((nt, x), _)) = ctxt.queue.pop() {
        let (id, maxsat) = handle(nt, x, ctxt);
        if let Some(solution) = id {
            handle_solution(solution, ctxt);
            return extract(solution, ctxt);
        }

        if cfg!(feature = "heuristic-linr") {
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
        ctxt.solids[nt].push(x);
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
        _ if children.len() == 2 && matches!(rule.ident(),"Add" | "Mul" | "Equals" | "And" | "Xor" | "Distinct" | "Or")=>  children[0] == children[1] 
        "Add" => {
            let [a, b] = children;
            match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                (_, Node::ConstInt(0, ty)) | (Node::ConstInt(0, ty), _) => {
                    return nt == ty.into_nt().unwrap();
                }
                _ => {}
            }

            ctxt.classes[*a].vals.iter().all(|v| *v == Value::Int(0)) || ctxt.classes[*b].vals.iter().all(|v| *v == Value::Int(0))
        }
        "Mul" =>  {
            let [a, b] = children;
            match (&ctxt.classes[*a].node, &ctxt.classes[*b].node) {
                (_, Node::ConstInt(0, ty) | Node::ConstInt(1, ty))
                | (Node::ConstInt(0, ty) | Node::ConstInt(1, ty), _) => {
                    return nt == ty.into_nt().unwrap();
                }
                _ => {}
            }            
            let a_vals = ctxt.classes[*a].vals;
            let b_vals = ctxt.classes[*b].vals;
            a_vals.iter().all(|v| *v == Value::Int(0)) || a_vals.iter().all(|v| *v == Value::Int(1)) || b_vals.iter().all(|v| *v == Value::Int(0)) || b_vals.iter().all(|v| *v == Value::Int(1))
        }
        _ => match rule.signature() {
            (_, Ty::Bool) if rule.children().len() > 1 => children.iter().all(|c| *c == children[0]),
            _ => false
        },
    }
}

fn grow_combinations()

fn grow(nt: usize, x: Id, ctxt: &mut Ctxt) -> (Option<Id>, usize) {
    let mut max_sat = 0;
    let nt_reached = ctxt.problem.nt_tc.reached_by(nt).clone();

    for (_, rule) in ctxt.problem.prod_rules() {
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
                    let ids = ctxt.problem.nt_tc
                        .reached_by(ty.into_nt().unwrap())
                        .clone();
                    (*pos, ids)
                })
                .collect();

            if rel_children.is_empty() || rel_children.iter().any(|(_, ids)| ids.is_empty()) {
                if remaining_children_nts
                    .iter()
                    .all(|(_, ty)| !matches!(ty, Ty::PRule(_)))
                {
                    let (id, is_sol, satcount) = add_node(base_prog.clone(), ctxt, None);
                    max_sat = max_sat.max(satcount);
                    if is_sol {
                        return (Some(id), max_sat);
                    }

                    for o in &nt_reached {
                        ctxt.solids[*o].push(id);
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
                new_children.sort_by_key(|(pos, _)| *pos);

                let child_ids: Vec<usize> =
                    new_children.iter().map(|(_, c)| *c).collect();

                if !prune(nt, rule, &child_ids, ctxt) {
                    let mut prog = base_prog.clone();

                    for (pos, c_idx) in &new_children {
                        let ty_nt = in_types[*pos].into_nt().unwrap();
                        prog.children_mut()[*pos] = Child::Hole(ty_nt, *c_idx);
                    }

                    let (id, is_sol, satcount) = add_node(prog, ctxt, None);
                    max_sat = max_sat.max(satcount);
                    if is_sol {
                        return (Some(id), max_sat);
                    }

                    for o in &nt_reached {
                        ctxt.solids[*o].push(id);
                    }
                }
            }
        }
    }

    (None, max_sat)
}

fn add_mode() {
    todo!();
}

