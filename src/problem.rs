use crate::*;

use indexmap::IndexMap;

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

    pub instvars: Vec<Box<[Id]>>,
}

struct Def {
    args: Vec<String>,
    expr: Expr,
}

// resolves "let" and "defined-funs"
// defs are not necessarily simplified, but varmap is.
fn simplify_expr(e: Expr, defs: &Map<String, Def>, varmap: &Map<String, Expr>) -> Expr {
    match e {
        Expr::Terminal(Terminal::Num(i)) => Expr::Terminal(Terminal::Num(i)),
        Expr::Terminal(Terminal::Bool(b)) => Expr::Terminal(Terminal::Bool(b)),
        Expr::Terminal(Terminal::Var(v)) => {
            if let Some(t) = varmap.get(&v) {
                t.clone()
            } else {
                Expr::Terminal(Terminal::Var(v))
            }
        },
        Expr::Operation { op, expr } => {
            if let Some(def) = defs.get(&op) {
                let mut ivarmap = Map::default();
                for (v, ex) in (def.args.iter()).zip(expr.into_iter()) {
                    let ex = simplify_expr(ex, defs, varmap);
                    ivarmap.insert(v.clone(), ex);
                }
                return simplify_expr(def.expr.clone(), defs, &ivarmap);
            }

            let expr: Vec<Expr> = expr.into_iter().map(|x| simplify_expr(x, defs, varmap)).collect();
            Expr::Operation { op, expr }
        }
        Expr::Let { bindings, body } => {
            let mut varmap = varmap.clone();
            for (var, ex) in bindings {
                let ex = simplify_expr(ex, defs, &varmap);
                varmap.insert(var, ex);
            }
            simplify_expr(*body, defs, &varmap)
        },
    }
}

fn sygus_expr_to_term(e: Expr, vars: &IndexMap<String, Ty>, progname: &str) -> (Term, Vec<Box<[Id]>>) {
    let mut t = Term { elems: Vec::new() };
    let mut instvars = Vec::new();
    sygus_expr_to_term_impl(e, vars, progname, &mut t, &mut instvars);
    (t, instvars)
}

fn sygus_expr_to_term_impl(e: Expr, vars: &IndexMap<String, Ty>, progname: &str, t: &mut Term, instvars: &mut Vec<Box<[Id]>>) -> Id {
    match e {
        Expr::Terminal(Terminal::Var(v)) => {
            let i = vars.iter().position(|x| *x.0 == *v).unwrap();
            let (_, ty) = vars.get_index(i).unwrap();
            match ty {
                Ty::Int =>  t.push(Node::VarInt(i)),
                Ty::Bool =>  t.push(Node::VarBool(i)),
            }
        },
        Expr::Terminal(Terminal::Bool(true)) => { t.push(Node::True) },
        Expr::Terminal(Terminal::Bool(false)) => { t.push(Node::False) },
        Expr::Terminal(Terminal::Num(i)) => { t.push(Node::ConstInt(i)) },
        Expr::Operation { op, expr } => {
            let exprs: Box<[Id]> = expr.iter().map(|x| sygus_expr_to_term_impl(x.clone(), vars, progname, t, instvars)).collect();
            let n = Node::parse(&*op, &*exprs).unwrap_or_else(|| {
                if op == progname {
                    instvars.push(exprs.iter().cloned().collect());
                    Node::VarInt(vars.len() + instvars.len() - 1)
                } else {
                    panic!("unknown node {op} of arity {}", exprs.len())
                }
            });
            t.push(n)
        },
        Expr::Let { bindings, body } => todo!(),
    }
}

pub fn mk_sygus_problem(f: &str) -> Problem {
    let s = std::fs::read_to_string(f).unwrap();

    let synth_problem = parse_synth(&s);

    let (parsed, _) = parse_sygus(&s).unwrap();

    build_sygus(parsed, synth_problem)
}

fn build_sygus(exprs: Vec<SyGuSExpr>, synth_problem: SynthProblem) -> Problem {
    assert_eq!(synth_problem.synthfuns.len(), 1);
    let synth_fun = synth_problem.synthfuns[0].clone();

    let progname = synth_problem.synthfuns.keys().next().unwrap().clone();
    let rettype = synth_fun.ret;

    let Some(SyGuSExpr::SynthFun(_, _, _, _, subgrammars)) =
        exprs.iter().filter(|x| matches!(x, SyGuSExpr::SynthFun(..))).cloned().next() else { panic!() };

    let argtypes: Vec<Ty> = synth_fun.args.iter().map(|(_, x)| *x).collect();

    let defs: Map<String, Def> = exprs.iter().filter_map(|x|
        if let SyGuSExpr::DefinedFun(f) = x {
            let def = Def {
                args: f.args.iter().map(|(x, _)| x.clone()).collect(),
                expr: f.expr.clone(),
            };
            Some((f.name.clone(), def))
        } else { None }
    ).collect();

    let vars = synth_fun.args.clone();

    let constraint: Expr = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(e.clone())
        } else { None }
    ).fold(Expr::Terminal(Terminal::Bool(true)), |x, y| Expr::Operation { op: format!("and"), expr: vec![x, y],} );

    let constraint_str = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(prettyprint(e))
        } else { None }
    ).fold(String::from("true"), |x, y| format!("(and {x} {y})"));

    let mut prod_rules = Vec::new();
    for g in subgrammars {
        for t in g.terminals {
            match t {
                Terminal::Num(i) => prod_rules.push(Node::ConstInt(i)),
                Terminal::Var(v) => {
                    let i = vars.get_index_of(&*v).unwrap();
                    match g.ty {
                        Ty::Int => prod_rules.push(Node::VarInt(i)),
                        Ty::Bool => prod_rules.push(Node::VarBool(i)),
                    }
                },
                _ => {},
            }
        }

        for n in g.nonterminals {
            let args: Vec<_> = n.args.iter().map(|_| 0).collect();
            if let Some(node) = Node::parse(&*n.op, &*args) {
                prod_rules.push(node);
            }
        }
    }

    let mut context: String = String::new();
    for expr in exprs.iter() {
        if let SyGuSExpr::DefinedFun(fun) = expr {
            context.push_str(&fun.stringify());
            context.push('\n');
        }
    }

    let context_vars = synth_problem.declared_vars.clone();

    for (name, ty) in context_vars.iter() {
        let ty = ty.to_string();
        context.push_str(&format!("(declare-fun {name} () {ty})\n"));
    }

    let constraint = simplify_expr(constraint, &defs, &Map::default());
    let (constraint, instvars) = sygus_expr_to_term(constraint, &context_vars, &progname);

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
