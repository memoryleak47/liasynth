use crate::*;

use indexmap::IndexMap;
use std::hash::Hash;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

#[derive(Clone)]
pub struct Problem {
    pub synth_problem: SynthProblem,
    pub synth_fun: SynthFun,

    pub argtypes: Vec<Ty>,
    pub rettype: Ty,

    pub progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    pub vars: IndexMap<String, Ty>,

    pub constraint: Term,
    pub constraint_str: String,

    // The ids of these Nodes will be nulled away.
    pub prod_rules: Box<[Node]>,

    pub context: String,
    pub context_vars: IndexMap<String, Ty>,

    // For each occurence i of a synthfun call, instvars[i] contains the Ids (indexed into problem.constraint.elems)
    // with which it is called.
    // During sat checking, this synthfun call is replaced by a special variable -- an instvar.
    pub instvars: Vec<Box<[Id]>>,
}

// resolves "let" and "defined-funs"
// defs are not necessarily simplified, but varmap is.
fn simplify_expr(e: Expr, defs: &IndexMap<String, DefinedFun>, varmap: &Map<String, Expr>) -> Expr {
    match e {
        Expr::ConstInt(i) => Expr::ConstInt(i),
        Expr::ConstBool(b) => Expr::ConstBool(b),
        Expr::Var(v) => {
            if let Some(t) = varmap.get(&v) {
                t.clone()
            } else {
                Expr::Var(v)
            }
        },
        Expr::DefinedFunCall(op, exprs) => {
            let def = &defs[&op];
            let mut ivarmap: Map<String, Expr> = Map::default();
            for ((v, _), ex) in (def.args.iter()).zip(exprs.into_iter()) {
                let ex = simplify_expr(ex, defs, varmap);
                ivarmap.insert(v.clone(), ex);
            }
            simplify_expr(def.expr.clone(), defs, &ivarmap)
        },
        Expr::SynthFunCall(op, exprs) => {
            let exprs: Vec<Expr> = exprs.into_iter().map(|x| simplify_expr(x, defs, varmap)).collect();
            Expr::SynthFunCall(op, exprs)
        },
        Expr::Op(op, exprs) => {
            let exprs: Vec<Expr> = exprs.into_iter().map(|x| simplify_expr(x, defs, varmap)).collect();
            Expr::Op(op, exprs)
        }
        Expr::Let(bindings, body) => {
            let mut varmap = varmap.clone();
            for (var, ex) in bindings {
                let ex = simplify_expr(ex, defs, &varmap);
                varmap.insert(var, ex);
            }
            simplify_expr(*body, defs, &varmap)
        },
    }
}

fn expr_to_term(e: Expr, vars: &IndexMap<String, Ty>, progname: &str) -> (Term, Vec<Box<[Id]>>) {
    let mut t = Term { elems: Vec::new() };
    let mut instvars = Vec::new();
    expr_to_term_impl(e, vars, progname, &mut t, &mut instvars);
    (t, instvars)
}

fn expr_to_term_impl(e: Expr, vars: &IndexMap<String, Ty>, progname: &str, t: &mut Term, instvars: &mut Vec<Box<[Id]>>) -> Id {
    match e {
        Expr::Var(v) => {
            let i = vars.iter().position(|x| *x.0 == *v).unwrap();
            let (_, ty) = vars.get_index(i).unwrap();
            match ty {
                Ty::Int => t.push(Node::VarInt(i)),
                Ty::Bool => t.push(Node::VarBool(i)),
            }
        },
        Expr::ConstBool(true) => { t.push(Node::True) },
        Expr::ConstBool(false) => { t.push(Node::False) },
        Expr::ConstInt(i) => { t.push(Node::ConstInt(i)) },
        Expr::Op(op, exprs) => {
            let exprs: Box<[Node]> = exprs.into_iter().map(|x| Node::PlaceHolder(expr_to_term_impl(x, vars, progname, t, instvars))).collect();
            let n = Node::parse(&*op, &*exprs).unwrap();
            t.push(n)
        },
        Expr::SynthFunCall(_name, exprs) => {
            let exprs: Box<[Id]> = exprs.into_iter().map(|x| expr_to_term_impl(x, vars, progname, t, instvars)).collect();
            instvars.push(exprs.iter().cloned().collect());
            t.push(Node::VarInt(vars.len() + instvars.len() - 1))
        },
        Expr::DefinedFunCall(..) => unreachable!("DefinedFunCalls should already be resolved!"),
        Expr::Let(..) => unreachable!("Lets should already be resolved!"),
    }
}

pub fn mk_sygus_problem(f: &str) -> Problem {
    let s = std::fs::read_to_string(f).unwrap();
    let synth_problem = parse_synth(&s);
    build_sygus(synth_problem)
}

fn parse_grammar_term(rule: &GrammarTerm, vars: &IndexMap<String, Ty>) -> Node {
    match rule {
        GrammarTerm::NonTerminal(_) => {
            // we'll iterate over the referenced non-terminal anyways.
            // Thus, no need to do it now again.
            Node::PlaceHolder(0)
        },
        GrammarTerm::Op(op, nts) => {
            let args: Vec<_> = nts.iter().map(|n| {
                parse_grammar_term(n, vars)
            }).collect();

            Node::parse(&*op, &*args).expect("Could not parse prod rule")
        },
        GrammarTerm::ConstInt(i) => Node::ConstInt(*i),
        GrammarTerm::ConstBool(true) => Node::True,
        GrammarTerm::ConstBool(false) => Node::False,
        GrammarTerm::SynthArg(v) => {
            let i = vars.get_index_of(&*v).unwrap();
            let ty = vars[v];
            match ty {
                Ty::Int => Node::VarInt(i),
                Ty::Bool => Node::VarBool(i),
            }
        },
        GrammarTerm::DefinedFunCall(f, args) => todo!("handle DefinedFunCalls in the grammar"),
    }
}

fn build_sygus(synth_problem: SynthProblem) -> Problem {
    assert_eq!(synth_problem.synthfuns.len(), 1);
    let synth_fun = synth_problem.synthfuns[0].clone();

    let progname = synth_problem.synthfuns.keys().next().unwrap().clone();
    let rettype = synth_fun.ret;

    let argtypes: Vec<Ty> = synth_fun.args.iter().map(|(_, x)| *x).collect();

    let defs: IndexMap<String, DefinedFun> = synth_problem.defined_funs.clone();

    let vars = synth_fun.args.clone();

    let mut constraint: Expr = synth_problem.constraints.get(0).cloned().unwrap_or_else(|| Expr::ConstBool(true));
    for c in synth_problem.constraints.iter().skip(1) {
        constraint = Expr::Op(String::from("and"), vec![constraint, c.clone()]);
    }

    let constraint_str = constraint.to_string();

    let mut prod_rules = Vec::new();
    for (_, ntdef) in synth_fun.nonterminal_defs.iter() {
        for rule in ntdef.prod_rules.iter() {
            let node = parse_grammar_term(rule, &vars);
            println!("{:?}", node);
            prod_rules.push(node);
        }
    }


    let mut context: String = String::new();
    for (_, def) in synth_problem.defined_funs.iter() {
        context.push_str(&format!("{def}\n"));
    }

    let context_vars = synth_problem.declared_vars.clone();

    for (name, ty) in context_vars.iter() {
        let ty = ty.to_string();
        context.push_str(&format!("(declare-fun {name} () {ty})\n"));
    }

    let constraint = simplify_expr(constraint, &defs, &Map::default());
    let (constraint, instvars) = expr_to_term(constraint, &context_vars, &progname);

    Problem {
        synth_problem,
        synth_fun,
        progname,
        argtypes,
        rettype,
        vars,
        constraint,
        constraint_str,
        prod_rules: prod_rules.into(),
        context,
        context_vars,
        instvars,
    }
}

fn show_val(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Bool(b) => b.to_string(),
    }
}

impl Problem {
    pub fn prod_rules(&self) -> &[Node] { &self.prod_rules }
}

impl Problem {
    pub fn verify(&self, term: &Term) -> Option<Sigma> {
        let retty = term.elems.last().unwrap().ty();
        if retty != self.rettype {
            let mut ret = Vec::new();
            for (v, ty) in self.context_vars.iter() {
                match ty {
                    Ty::Int => ret.push(Value::Int(0)),
                    Ty::Bool => ret.push(Value::Bool(true)),
                }
            }
            return Some(ret);
        }

        let mut query = self.context.clone();
        let retty = retty.to_string();
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for (var, ty) in self.vars.iter() {
            query.push_str(&format!("({var} {}) ", ty.to_string()));
        }
        let term = term_to_z3(term, &self.vars.keys().cloned().collect::<Box<[_]>>());
        query.push_str(&format!(") {retty} {term})\n"));

        let constraint_str = &self.constraint_str;
        query.push_str(&format!("(assert (not {constraint_str}))\n"));

        let config = z3::Config::new();
        let ctxt = z3::Context::new(&config);
        let mut solver = z3::Solver::new(&ctxt);
        // println!("VERIFY-QUERY: {}", &query);
        solver.from_string(query);
        // println!("VERIFY-SMT: {}", solver.to_smt2());

        if solver.check() == z3::SatResult::Sat {
            let ce = solver.get_model().unwrap();
            let mut sigma = Sigma::new();
            for (var, ty) in &self.context_vars {
                if matches!(ty, Ty::Int) {
                    let z3var = z3::ast::Int::new_const(&ctxt, var.to_string());
                    let z3val = ce.eval(&z3var, true);
                    sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
                } else {
                    let z3var = z3::ast::Bool::new_const(&ctxt, var.to_string());
                    let z3val = ce.eval(&z3var, true);
                    sigma.push(Value::Bool(z3val.unwrap().as_bool().unwrap()));
                };
            }
            Some(sigma)
        } else { None }
    }
}
