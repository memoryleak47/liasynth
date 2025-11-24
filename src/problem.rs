use crate::*;

use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub struct Problem {
    pub synth_problem: SynthProblem,
    pub synth_fun: SynthFun,

    pub argtypes: Vec<Ty>,
    pub rettype: Ty,
    // Vec of possible nonterminals that are valid
    // Vec in cases of the 'start' nonterminal referencing other nonterminals
    pub rettys: Vec<Ty>,
    pub nt_mapping: HashMap<Ty, Ty>,
    pub progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    pub vars: IndexMap<String, Ty>,

    pub constraint: Term,
    pub constraint_str: String,

    // The ids of these Nodes will be nulled away.
    pub prod_rules: Box<[(usize, Node)]>,

    pub nt_tc: TransitiveClosure,

    pub context: String,
    pub context_vars: IndexMap<String, Ty>,

    // For each occurence i of a synthfun call, instvars[i] contains the Ids (indexed into problem.constraint.elems)
    // with which it is called.
    // During sat checking, this synthfun call is replaced by a special variable -- an instvar.
    pub instvars: Vec<Box<[Id]>>,
}

fn expr_to_term(
    e: Expr,
    defs: &IndexMap<String, DefinedFun>,
    vars: &IndexMap<String, Ty>,
    progname: &str,
    rettype: Ty,
) -> (Term, Vec<Box<[Id]>>) {
    let mut t = Term { elems: Vec::new() };
    let mut instvars = IndexMap::new();
    let tmpvars = IndexMap::default();
    expr_to_term_impl(e, defs, &tmpvars, vars, progname, &mut t, &mut Map::default(), &mut instvars, rettype);
    let instvars = instvars.into_iter().map(|(x, _)| x).collect();
    (t, instvars)
}

fn expr_to_term_impl(
    e: Expr,
    defs: &IndexMap<String, DefinedFun>,
    tmpvars: &IndexMap<String, Id>, // variables created by "let" or defined-fun args.
    vars: &IndexMap<String, Ty>, // global variables created by "declare-var".
    progname: &str,
    t: &mut Term,
    hashcons: &mut Map<Node, Id>,
    instvars: &mut IndexMap<Box<[Id]>, Id>,
    rettype: Ty,
) -> Id {
    let hashconsed_push = |t: &mut Term, n: Node, hashcons: &mut Map<Node, Id>| -> Id {
        if let Some(x) = hashcons.get(&n) {
            return *x;
        }
        let i = t.push(n.clone());
        hashcons.insert(n, i);
        i
    };
    match e {
        Expr::Var(v) => {
            if let Some(x) = tmpvars.get(&v) {
                return *x;
            }
            let i = vars.iter().position(|x| *x.0 == *v).unwrap();
            let (_, ty) = vars.get_index(i).unwrap();
            let n = match ty {
                Ty::Int => Node::VarInt(i, Ty::Int),
                Ty::Bool => Node::VarBool(i, Ty::Bool),
                _ => panic!("should not happen"),
            };
            hashconsed_push(t, n, hashcons)
        }
        Expr::ConstBool(true) => hashconsed_push(t, Node::True(Ty::Bool), hashcons),
        Expr::ConstBool(false) => hashconsed_push(t, Node::False(Ty::Bool), hashcons),
        Expr::ConstInt(i) => hashconsed_push(t, Node::ConstInt(i, Ty::Int), hashcons),
        Expr::Op(op, exprs) => {
            let exprs: Box<[Node]> = exprs
                .into_iter()
                .map(|x| {
                    Node::PlaceHolder(
                        expr_to_term_impl(x, defs, tmpvars, vars, progname, t, hashcons, instvars, rettype),
                        Ty::Int,
                    )
                })
                .collect();
            let n = Node::parse(&*op, &*exprs).unwrap();
            hashconsed_push(t, n, hashcons)
        }
        Expr::SynthFunCall(_name, exprs) => {
            let exprs: Box<[Id]> = exprs
                .into_iter()
                .map(|x| expr_to_term_impl(x, defs, tmpvars, vars, progname, t, hashcons, instvars, rettype))
                .collect();
            if let Some(x) = instvars.get(&exprs) {
                return *x;
            }
            let i = t.push(Node::VarInt(instvars.len() + vars.len() - 1, rettype));
            instvars.insert(exprs.iter().cloned().collect(), i);
            i
        }
        Expr::DefinedFunCall(op, exprs) => {
            let exprs: Box<[Id]> = exprs
                .into_iter()
                .map(|x| expr_to_term_impl(x, defs, tmpvars, vars, progname, t, hashcons, instvars, rettype))
                .collect();
            let def = &defs[&op];
            let mut ivarmap: IndexMap<String, Id> = IndexMap::default();
            for ((v, _), ex) in (def.args.iter()).zip(exprs.into_iter()) {
                ivarmap.insert(v.clone(), ex);
            }
            expr_to_term_impl(def.expr.clone(), defs, &ivarmap, vars, progname, t, hashcons, instvars, rettype)
        }
        Expr::Let(bindings, body) => {
            let mut varmap = tmpvars.clone();
            for (var, ex) in bindings {
                let ex = expr_to_term_impl(ex, defs, &varmap, vars, progname, t, hashcons, instvars, rettype);
                varmap.insert(var, ex);
            }
            expr_to_term_impl(*body, defs, &varmap, vars, progname, t, hashcons, instvars, rettype)
        }
    }
}

pub fn mk_sygus_problem(f: &str) -> Problem {
    let s = std::fs::read_to_string(f).unwrap();
    let synth_problem = parse_synth(&s);
    build_sygus(synth_problem)
}

fn parse_grammar_term(
    nt: usize,
    rule: &GrammarTerm,
    vars: &IndexMap<String, Ty>,
    nonterminals: &IndexMap<String, Ty>,
    refs: &IndexMap<usize, Vec<String>>,
) -> Option<Node> {
    match rule {
        GrammarTerm::NonTerminal(n, ty) => {
            // we'll iterate over the referenced non-terminal anyways.
            // Thus, no need to do it now again.
            let t = nonterminals.get_index_of(n)?;
            let mut valids: usize = 1usize << t;

            if let Some(vs) = refs.get(&t) {
                for v in vs {
                    let f = nonterminals.get_index_of(v)?;
                    valids |= 1usize << f;
                }
            }

            Some(Node::PlaceHolder(0, Ty::PRule(valids)))
        }
        GrammarTerm::Op(op, nts) => {
            let args: Vec<_> = nts
                .iter()
                .flat_map(|n| parse_grammar_term(nt, n, vars, nonterminals, refs))
                .collect();
            Some(
                Node::parse_prod(&*op, &*args, Ty::NonTerminal(nt))
                    .expect("Could not parse prod rule"),
            )
        }
        GrammarTerm::DefinedFunCall(op, template, nts) => {
            let args: Vec<_> = nts
                .iter()
                .flat_map(|n| parse_grammar_term(nt, n, vars, nonterminals, refs))
                .collect();
            Some(
                Node::parse_prod(&*template, &*args, Ty::NonTerminal(nt)).unwrap_or_else(|| {
                    panic!(
                        "Could not parse prod rule: template: {:?}, args: {:?}",
                        template, args
                    )
                }),
            )
        }

        GrammarTerm::ConstInt(i, ty) => Some(Node::ConstInt(*i, *ty)),
        GrammarTerm::ConstBool(true, ty) => Some(Node::True(*ty)),
        GrammarTerm::ConstBool(false, ty) => Some(Node::False(*ty)),
        GrammarTerm::SynthArg(v, tty) => {
            let i = vars.get_index_of(&*v).unwrap();
            let ty = vars[v];
            match ty {
                Ty::Int => Some(Node::VarInt(i, *tty)),
                Ty::Bool => Some(Node::VarBool(i, *tty)),
                _ => panic!("should never happen"),
            }
        }
    }
}

#[derive(Default, Clone)]
pub struct TransitiveClosure {
    ancestors: Vec<Vec<usize>>,
}

impl TransitiveClosure {
    pub fn new(n: usize) -> Self {
        let mut ancestors = vec![Vec::new(); n];
        for i in 0..n {
            ancestors[i].push(i);
        }
        Self { ancestors }
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.ancestors[to].push(from);

        let from_ancestors: Vec<_> = self.ancestors[from].iter().copied().collect();
        for ancestor in from_ancestors {
            self.ancestors[to].push(ancestor);
        }
    }

    pub fn reached_by(&self, node: usize) -> &Vec<usize> {
        &self.ancestors[node]
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

    let mut constraint: Expr = synth_problem
        .constraints
        .get(0)
        .cloned()
        .unwrap_or_else(|| Expr::ConstBool(true));
    for c in synth_problem.constraints.iter().skip(1) {
        constraint = Expr::Op(String::from("and"), vec![constraint, c.clone()]);
    }

    let constraint_str = constraint.to_string();

    let mut nt_mapping = HashMap::new();
    let mut rettys = Vec::new();
    let mut prod_rules = Vec::new();

    let mut tc = TransitiveClosure::new(synth_fun.nonterminal_defs.len());

    for (n, (_, ntdef)) in synth_fun.nonterminal_defs.iter().enumerate() {
        nt_mapping.insert(Ty::NonTerminal(n), ntdef.ty);
        if n == 0 {
            rettys.push(Ty::NonTerminal(0))
        }
        for rule in ntdef.prod_rules.iter() {
            if let GrammarTerm::NonTerminal(s, _) = rule {
                let ont = synth_fun.nonterminal_defs.get_index_of(s).unwrap();
                tc.add_edge(n, ont);
            }
            if n == 0 {
                if let GrammarTerm::NonTerminal(n, _) = rule {
                    let m = synth_fun.nonterminal_defs.get_index_of(&n.clone()).unwrap();
                    rettys.push(Ty::NonTerminal(m));
                }
            }
            if let Some(node) = parse_grammar_term(
                n,
                rule,
                &vars,
                &synth_fun.nonterminals,
                &synth_fun.nonterminal_refs,
            ) {
                prod_rules.push((n, node));
            };
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

    let (constraint, instvars) = {
        time_block!("expr_to_term");
        expr_to_term(constraint, &defs, &context_vars, &progname, rettype)
    };

    Problem {
        synth_problem,
        synth_fun,
        progname,
        argtypes,
        rettype,
        rettys,
        nt_mapping,
        vars,
        constraint,
        constraint_str,
        prod_rules: prod_rules.into(),
        nt_tc: tc,
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
    pub fn prod_rules(&self) -> &[(usize, Node)] {
        &self.prod_rules
    }
}

impl Problem {
    pub fn verify(&self, term: &Term) -> Option<Sigma> {
        time_block!("problem.verify");
        let mut query = self.context.clone();
        let retty = self.rettype.to_string();
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for (var, ty) in self.vars.iter() {
            query.push_str(&format!("({var} {}) ", ty.to_string()));
        }
        let term = term_to_z3(term, &self.vars.keys().cloned().collect::<Box<[_]>>());
        query.push_str(&format!(") {retty} {term})\n"));

        let constraint_str = &self.constraint_str;
        query.push_str(&format!("(assert (not {constraint_str}))\n"));

        let mut solver = z3::Solver::new();
        // println!("VERIFY-QUERY: {}", &query);
        solver.from_string(query);
        // println!("VERIFY-SMT: {}", solver.to_smt2());

        if solver.check() == z3::SatResult::Sat {
            let ce = solver.get_model().unwrap();
            let mut sigma = Sigma::new();
            for (var, ty) in &self.context_vars {
                if matches!(ty, Ty::Int) {
                    let z3var = z3::ast::Int::new_const(var.to_string());
                    let z3val = ce.eval(&z3var, true);
                    sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
                } else {
                    let z3var = z3::ast::Bool::new_const(var.to_string());
                    let z3val = ce.eval(&z3var, true);
                    sigma.push(Value::Bool(z3val.unwrap().as_bool().unwrap()));
                };
            }
            Some(sigma)
        } else {
            None
        }
    }
}
