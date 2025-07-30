use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    argtypes: Vec<Ty>,
    rettype: Ty,

    progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    vars: Vec<String>,

    constraint: Term,

    // The ids of these Nodes will be nulled away.
    prod_rules: Box<[Node]>,

    context: String,
    context_vars: Vec<String>,

    accesses: Box<[Box<[Var]>]>,
}

fn sygus_expr_to_term(e: Expr, lets: &mut Vec<(String, Term)>, vars: &[String], progname: &str) -> Term {
    let mut t = Term { elems: Vec::new() };
    sygus_expr_to_term_impl(e, lets, vars, progname, &mut t);
    t
}

fn sygus_expr_to_term_impl(e: Expr, lets: &mut Vec<(String, Term)>, vars: &[String], progname: &str, t: &mut Term) -> Id {
    match e {
        Expr::Terminal(Terminal::Var(v)) => {
            let i = vars.iter().position(|x| *x == *v).unwrap();
            t.push(Node::Var(i))
        },
        Expr::Terminal(Terminal::Bool(true)) => { t.push(Node::True) },
        Expr::Terminal(Terminal::Bool(false)) => { t.push(Node::False) },
        Expr::Terminal(Terminal::Num(i)) => { t.push(Node::ConstInt(i)) },
        Expr::Operation { op, expr } => {
            let exprs: Box<[Id]> = expr.iter().map(|x| sygus_expr_to_term_impl(x.clone(), lets, vars, progname, t)).collect();
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
                (prog, args) if prog == progname => Node::SynthCall(args.iter().copied().collect()),
                (x, l) => todo!("unknown node {x} of arity {}", l.len()),
            };
            t.push(n)
        },
        Expr::Let { bindings, body } => todo!(),
    }
}

pub fn sygus_problem(f: &str) -> (impl Problem, impl Oracle) {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    let pao = build_sygus(parsed);

    (pao.clone(), pao)
}

fn build_sygus(exprs: Vec<SyGuSExpr>) -> SygusProblemAndOracle {
    let Some(SyGuSExpr::SynthFun(progname, argtypes, rettype, _, subgrammars)) =
        exprs.iter().filter(|x| matches!(x, SyGuSExpr::SynthFun(..))).cloned().next() else { panic!() };

    let mut vars: Vec<String> = Vec::new();

    let constraint: Expr = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(e.clone())
        } else { None }
    ).fold(Expr::Terminal(Terminal::Bool(true)), |x, y| Expr::Operation { op: format!("and"), expr: vec![x, y],} );

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

    let constraint = sygus_expr_to_term(constraint, &mut Vec::new(), &context_vars, &progname);

    let mut accesses = Vec::new();
    for x in constraint.elems.iter() {
        if let Node::SynthCall(args) = x {
            let access = args.iter().map(|a|
                match &constraint.elems[*a] {
                    Node::Var(v) => *v,
                    _ => panic!("Can only depend on variables!"),
                }).collect();
            accesses.push(access);
        }
    }
    let accesses = accesses.into();

    SygusProblemAndOracle {
        progname,
        argtypes: argtypes.into_iter().map(|(_, x)| x).collect(),
        rettype,
        vars,
        constraint,
        prod_rules: prod_rules.into(),
        context,
        context_vars,
        accesses,
    }
}

fn show_val(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Bool(b) => b.to_string(),
    }
}

impl Problem for SygusProblemAndOracle {
    fn prod_rules(&self) -> &[Node] { &self.prod_rules }
    fn sat(&self, term: &Term, sigma: &Sigma) -> bool {
        if term.elems.last().unwrap().ty() != self.rettype {
            return false;
        }
        if !sigma.iter().zip(self.argtypes.iter()).all(|(val, ty)| val.ty() == *ty) {
            return false;
        }

        let vars: Box<[_]> = (0..self.vars.len()).collect();
        eval_term(&self.constraint, sigma, term) == Value::Bool(true)
    }

    fn accesses(&self) -> &[Box<[Var]>] {
        &self.accesses
    }
}

impl Oracle for SygusProblemAndOracle {
    fn verify(&self, term: &Term) -> Option<Sigma> {
        let retty = term.elems.last().unwrap().ty();
        if retty != self.rettype {
            return Some(vec![Value::Int(0); self.vars.len()]);
        }

        let mut query = self.context.clone();
        let retty = retty.to_string();
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let term = term_to_z3(term.elems.len()-1, term, &self.context_vars, &self.progname);
        query.push_str(&format!(") {retty} {term})\n"));

        let mut constr = term_to_z3(self.constraint.elems.len()-1, &self.constraint, &self.context_vars, &self.progname);
        query.push_str(&format!("(assert (not {constr}))\n"));

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
                let z3var = z3::ast::Int::new_const(&ctxt, var.to_string());
                let z3val = ce.eval(&z3var, true); // TODO model completion?
                sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
            }
            Some(sigma)
        } else { None }
    }
}
