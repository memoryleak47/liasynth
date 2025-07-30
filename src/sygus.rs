use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    argtypes: Vec<Ty>,
    rettype: Ty,

    progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    vars: Vec<String>,

    // These strings will be interpreted by Z3.
    constraint: String,

    // The ids of these Nodes will be nulled away.
    prod_rules: Box<[Node]>,

    context: String,
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

    let constraints_vec: Box<[String]> = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(prettyprint(&e))
        } else { None }
    ).collect();

    let constraint_s = constraints_vec.join(" ");
    let constraint = format!("(and {constraint_s})");

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
    for expr in exprs.iter() {
        if let SyGuSExpr::DefinedFun(fun) = expr {
            context.push_str(&fun.stringify());
            context.push('\n');
        }
        if let SyGuSExpr::DeclaredVar(name, ty) = expr {
            if vars.contains(name) { continue }

            let ty = ty.to_string();
            context.push_str(&format!("(declare-fun {name} () {ty})\n"));
        }
    }

    SygusProblemAndOracle {
        progname,
        argtypes: argtypes.into_iter().map(|(_, x)| x).collect(),
        rettype,
        vars,
        constraint,
        prod_rules: prod_rules.into(),
        context,
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
    fn sat(&self, val: &Value, sigma: &Sigma) -> bool {
        if val.ty() != self.rettype {
            return false;
        }
        if !sigma.iter().zip(self.argtypes.iter()).all(|(val, ty)| val.ty() == *ty) {
            return false;
        }

        let retty = val.ty().to_string();
        let mut query = self.context.clone();
        for (var, val2) in self.vars.iter().zip(sigma.iter()) {
            let val2 = show_val(val2);
            query.push_str(&format!("(define-fun {var} () Int {val2})\n"));
        }
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let val = show_val(val);
        query.push_str(&format!(") {retty} {val})\n"));
        let constr = &self.constraint;
        query.push_str(&format!("(assert {constr})\n"));

        let config = z3::Config::new();
        let ctxt = z3::Context::new(&config);
        let mut solver = z3::Solver::new(&ctxt);
        // println!("SAT-QUERY: {}", &query);
        solver.from_string(query);
        // println!("SAT-SMT: {}", solver.to_smt2());

        solver.check() == z3::SatResult::Sat
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
        for var in self.vars.iter() {
            query.push_str(&format!("(declare-fun {var} () Int)\n"));
        }
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let term = term_to_z3(term.elems.len()-1, term, &self.vars);
        query.push_str(&format!(") {retty} {term})\n"));
        let constr = &self.constraint;
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
            for var in &self.vars {
                let z3var = z3::ast::Int::new_const(&ctxt, var.to_string());
                let z3val = ce.eval(&z3var, true); // TODO model completion?
                sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
            }
            Some(sigma)
        } else { None }
    }
}
