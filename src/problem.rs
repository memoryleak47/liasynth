use crate::*;

#[derive(Clone)]
pub struct Problem {
    pub argtypes: Vec<Ty>,
    pub rettype: Ty,

    pub progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    pub vars: Vec<String>,

    pub constraint: Term,
    pub constraint_str: String,

    // The ids of these Nodes will be nulled away.
    pub prod_rules: Box<[Node]>,

    pub context: String,
    pub context_vars: Vec<String>,

    pub instvars: Vec<Box<[Id]>>,
}

struct Def {
    args: Vec<String>,
    expr: Expr,
}

// resolves "let" and "defined-funs"
fn simplify_expr(e: Expr, defs: &Map<String, Def>, done_something: &mut bool) -> Expr {
    match e {
        Expr::Terminal(a) => Expr::Terminal(a),
        Expr::Operation { op, expr } => {
            let expr: Vec<Expr> = expr.iter().map(|x| simplify_expr(x.clone(), defs, done_something)).collect();
            if let Some(def) = defs.get(&op) {
                *done_something = true;
                let mut bb = def.expr.clone();
                for (a, b) in (def.args.iter()).zip(expr.iter()) {
                    bb = expr_subst(bb, a, b);
                }
                bb
            } else {
                Expr::Operation { op, expr }
            }
        }
        Expr::Let { bindings, body } => {
            *done_something = true;
            let mut body: Expr = *body;
            for (var, expr) in bindings {
                body = expr_subst(body, &var, &expr);
            }
            body
        },
    }
}

// computes e[v := t]
fn expr_subst(e: Expr, v: &str, t: &Expr) -> Expr {
    match e {
        Expr::Terminal(Terminal::Var(v2)) if v == v2 => {
            t.clone()
        },
        Expr::Operation { op, expr } => {
            let expr: Vec<Expr> = expr.into_iter().map(|x| expr_subst(x, v, t)).collect();
            Expr::Operation { op, expr }
        },
        Expr::Terminal(a) => Expr::Terminal(a),
        Expr::Let { bindings, body } => todo!(),
    }
}

fn sygus_expr_to_term(e: Expr, vars: &[String], progname: &str) -> (Term, Vec<Box<[Id]>>) {
    let mut t = Term { elems: Vec::new() };
    let mut instvars = Vec::new();
    sygus_expr_to_term_impl(e, vars, progname, &mut t, &mut instvars);
    (t, instvars)
}

fn sygus_expr_to_term_impl(e: Expr, vars: &[String], progname: &str, t: &mut Term, instvars: &mut Vec<Box<[Id]>>) -> Id {
    match e {
        Expr::Terminal(Terminal::Var(v)) => {
            let i = vars.iter().position(|x| *x == *v).unwrap();
            t.push(Node::Var(i))
        },
        Expr::Terminal(Terminal::Bool(true)) => { t.push(Node::True) },
        Expr::Terminal(Terminal::Bool(false)) => { t.push(Node::False) },
        Expr::Terminal(Terminal::Num(i)) => { t.push(Node::ConstInt(i)) },
        Expr::Operation { op, expr } => {
            let exprs: Box<[Id]> = expr.iter().map(|x| sygus_expr_to_term_impl(x.clone(), vars, progname, t, instvars)).collect();
            let n = match (&*op, &*exprs) {
                ("+", &[x, y]) => Node::Add([x, y]),
                ("-", &[x, y]) => Node::Sub([x, y]),
                ("mul", &[x, y]) => Node::Mul([x, y]),
                ("div", &[x, y]) => Node::Div([x, y]),
                ("mod", &[x, y]) => Node::Mod([x, y]),
                ("abs", &[x]) => Node::Abs([x]),
                ("-", &[x]) => Node::Neg([x]),
                ("=>", &[x, y]) => Node::Implies([x, y]),
                ("ite", &[x, y, z]) => Node::Ite([x, y, z]),
                ("and", &[x, y]) => Node::And([x, y]),
                ("or", &[x, y]) => Node::Or([x, y]),
                ("xor", &[x, y]) => Node::Xor([x, y]),
                ("not", &[x]) => Node::Not([x]),
                ("true", &[]) => Node::True,
                ("false", &[]) => Node::False,
                ("<", &[x, y]) => Node::Lt([x, y]),
                ("<=", &[x, y]) => Node::Lte([x, y]),
                (">", &[x, y]) => Node::Gt([x, y]),
                (">=", &[x, y]) => Node::Gte([x, y]),
                ("=", &[x, y]) => Node::Equals([x, y]),
                ("distinct", &[x, y]) => Node::Distinct([x, y]),
                (prog, args) if prog == progname => {
                    instvars.push(args.iter().cloned().collect());
                    Node::Var(vars.len() + instvars.len() - 1)
                },
                (x, l) => todo!("unknown node {x} of arity {}", l.len()),
            };
            t.push(n)
        },
        Expr::Let { bindings, body } => todo!(),
    }
}

pub fn mk_sygus_problem(f: &str) -> Problem {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    build_sygus(parsed)
}

fn build_sygus(exprs: Vec<SyGuSExpr>) -> Problem {
    let Some(SyGuSExpr::SynthFun(progname, argtypes, rettype, _, subgrammars)) =
        exprs.iter().filter(|x| matches!(x, SyGuSExpr::SynthFun(..))).cloned().next() else { panic!() };

    let defs: Map<String, Def> = exprs.iter().filter_map(|x|
        if let SyGuSExpr::DefinedFun(f) = x {
            let def = Def {
                args: f.args.iter().map(|(x, _)| x.clone()).collect(),
                expr: f.expr.clone(),
            };
            Some((f.name.clone(), def))
        } else { None }
    ).collect();

    let mut vars: Vec<String> = Vec::new();

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
                    prod_rules.push(Node::Var(vars.len()));
                    vars.push(v.to_string());
                },
                _ => {},
            }
        }

        for n in g.nonterminals {
            match &*n.op {
                "+" => prod_rules.push(Node::Add([0, 0])),
                "-" => prod_rules.push(Node::Sub([0, 0])),
                "*" => prod_rules.push(Node::Mul([0, 0])),
                "div" => prod_rules.push(Node::Div([0, 0])),
                "mod" => prod_rules.push(Node::Mod([0, 0])),
                "ite" => prod_rules.push(Node::Ite([0, 0, 0])),
                "<" => prod_rules.push(Node::Lt([0, 0])),
                "<=" => prod_rules.push(Node::Lte([0, 0])),
                ">" => prod_rules.push(Node::Gt([0, 0])),
                ">=" => prod_rules.push(Node::Gte([0, 0])),
                "=" => prod_rules.push(Node::Equals([0, 0])),
                "abs" => prod_rules.push(Node::Abs([0])),
                _ => {},
            }
        }
    }

    let mut context: String = String::new();
    let mut context_vars: Vec<String> = Vec::new();
    for expr in exprs.iter() {
        if let SyGuSExpr::DefinedFun(fun) = expr {
            context.push_str(&fun.stringify());
            context.push('\n');
        }
        if let SyGuSExpr::DeclaredVar(name, ty) = expr {

            let ty = ty.to_string();
            context_vars.push(name.clone());
            context.push_str(&format!("(declare-fun {name} () {ty})\n"));
        }
    }

    let mut constraint = constraint.clone();
    loop {
        let mut b = false;
        constraint = simplify_expr(constraint, &defs, &mut b);
        if !b { break }
    }
    let (constraint, instvars) = sygus_expr_to_term(constraint, &context_vars, &progname);

    Problem {
        progname,
        argtypes: argtypes.into_iter().map(|(_, x)| x).collect(),
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
            return Some(vec![Value::Int(0); self.context_vars.len()]);
        }

        let mut query = self.context.clone();
        let retty = retty.to_string();
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let term = term_to_z3(term, &self.vars);
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
            for var in &self.context_vars {
                // TODO examples/LIA/unbdd_inv_gen_term2.sl has a boolean-typed context var. This one assumes it's always int.
                let z3var = z3::ast::Int::new_const(&ctxt, var.to_string());
                let z3val = ce.eval(&z3var, true); // TODO model completion?
                sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
            }
            Some(sigma)
        } else { None }
    }
}
