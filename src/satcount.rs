use crate::*;

const USE_INHOUSE_SATCOUNT: bool = true;

pub fn satcount(nt: usize, x: Id, ctxt: &mut Ctxt, idxs: Option<Vec<usize>>) -> u64 {
    GLOBAL_STATS.lock().unwrap().programs_checked += 1;
    let ty = ctxt.classes[x].node.ty();
    if ctxt
        .problem
        .nt_mapping
        .get(&ty)
        .expect("this never happens")
        != &ctxt.problem.rettype
    {
        return 0;
    }
    let no_vals = ctxt.small_sigmas.len() / ctxt.big_sigmas.len();

    if let Some(idxs) = idxs {
        let r = satisfy(nt, x, idxs.iter().cloned(), ctxt);
        for (pos, &i) in idxs.iter().enumerate() {
            let start = i * no_vals;
            let vchunk = &ctxt.classes[x].vals[start..start + no_vals];
            ctxt.cxs_cache[i].insert(Box::<[Value]>::from(vchunk), r[pos]);
        }

        return idxs.iter().zip(r.iter()).fold(
            0u64,
            |acc, (i, &val)| {
                if val { acc | (1 << i) } else { acc }
            },
        );
    }

    let r = satisfy(nt, x, 0..ctxt.big_sigmas.len(), ctxt);
    for (i, (vchunk, &res)) in ctxt.classes[x]
        .vals
        .chunks_exact(no_vals)
        .zip(r.iter())
        .enumerate()
    {
        ctxt.cxs_cache[i].insert(Box::<[Value]>::from(vchunk), res);
    }

    r.iter()
        .enumerate()
        .fold(064, |acc, (i, &val)| if val { acc | (1 << i) } else { acc })
}

pub fn satisfy(
    nt: usize,
    x: Id,
    ce_indices: impl IntoIterator<Item = usize>,
    ctxt: &Ctxt,
) -> Vec<bool> {
    if USE_INHOUSE_SATCOUNT {
        satisfy_inhouse(nt, x, ce_indices, ctxt)
    } else {
        satisfy_z3(x, ce_indices, ctxt)
    }
}

pub fn satisfy_inhouse_incr(ty: Ty, vals: &Box<[Value]>, id: usize, ctxt: &Ctxt) -> bool {
    // time_block!("satisfy_inhouse");

    if ctxt
        .problem
        .nt_mapping
        .get(&ty)
        .expect("this never happens")
        != &ctxt.problem.rettype
    {
        return false;
    }

    let big_sigma = &ctxt.big_sigmas[id];
    let indices = &ctxt.sigma_indices[id];

    let mut sigma = big_sigma.clone();
    // This is a huge sigma. It's a
    // - big sigma (all variables from the constraints), plus
    // - one variable per invocation of the synthfun

    for i in indices {
        sigma.push(vals[*i].clone());
    }

    let v = eval_term(&ctxt.problem.constraint, &sigma).unwrap();
    to_bool(v)
}

pub fn satisfy_inhouse(
    nt: usize,
    id: Id,
    ce_indices: impl IntoIterator<Item = usize>,
    ctxt: &Ctxt,
) -> Vec<bool> {
    // time_block!("satisfy_inhouse");

    if ctxt.problem.nt_mapping[&Ty::NonTerminal(nt)] != ctxt.problem.rettype {
        panic!("r?");
        return Vec::new();
    }

    let vals = &ctxt.classes[id].vals;

    let mut out = Vec::new();

    for idx in ce_indices {
        let big_sigma = &ctxt.big_sigmas[idx];
        let indices = &ctxt.sigma_indices[idx];

        let mut sigma = big_sigma.clone();
        // This is a huge sigma. It's a
        // - big sigma (all variables from the constraints), plus
        // - one variable per invocation of the synthfun

        for i in indices {
            sigma.push(vals[*i].clone());
        }

        let v = eval_term(&ctxt.problem.constraint, &sigma).unwrap();
        out.push(to_bool(v));
    }
    out
}

pub fn satisfy_z3(x: Id, ce_indices: impl IntoIterator<Item = usize>, ctxt: &Ctxt) -> Vec<bool> {
    // time_block!("satisfy_z3");

    let term = &extract(x, ctxt);
    let p = &ctxt.problem;
    let mut results = Vec::new();

    let mut query = p.context.clone();
    let retty = p.rettype.to_string();
    let progname = &p.progname;
    query.push_str(&format!("(define-fun {progname} ("));
    for (var, ty) in p.vars.iter() {
        query.push_str(&format!("({var} {}) ", ty.to_string()));
    }
    let term = term_to_z3(term, &p.vars.keys().cloned().collect::<Box<[_]>>());
    // println!("testing {term}");
    query.push_str(&format!(") {retty} {term})\n"));
    let constraint_str = &p.constraint_str;
    query.push_str(&format!("(assert {constraint_str})\n"));

    let solver = z3::Solver::new();
    solver.from_string(query);

    let mut sat_count = 0;
    for idx in ce_indices {
        let ce = &ctxt.big_sigmas[idx];

        let mut assumps = Vec::new();
        for ((var, ty), val) in p.context_vars.iter().zip(ce.into_iter()) {
            let sym = z3::ast::Int::new_const(var.to_string());
            let lit = match (ty, val) {
                (Ty::Int, Value::Int(v)) => sym.eq(&z3::ast::Int::from_i64(*v)),
                (Ty::Bool, Value::Bool(v)) => {
                    let b = z3::ast::Bool::new_const(var.to_string());
                    b.iff(&z3::ast::Bool::from_bool(*v))
                }
                _ => panic!("na"),
            };
            assumps.push(lit);
        }

        let assumps_refs: &[z3::ast::Bool] = assumps.as_slice();
        results.push(solver.check_assumptions(&assumps_refs) == z3::SatResult::Sat);
    }
    results
}
