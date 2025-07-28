use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    progname: String,

    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    vars: Vec<String>,

    // These strings will be interpreted by Z3.
    constraint: String,

    // The ids of these Nodes will be nulled away.
    prod_rules: Box<[Node]>,
}

pub fn sygus_problem(f: &str) -> (impl Problem, impl Oracle) {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    let pao = build_sygus(parsed);

    (pao.clone(), pao)
}

fn build_sygus(exprs: Vec<SyGuSExpr>) -> SygusProblemAndOracle {
    let (progname, subgrammars): (String, Vec<SubGrammar>) =
        exprs.iter().filter_map(|x|
            if let SyGuSExpr::SynthFun(progname, .., subgrammars) = x {
                Some((progname.clone(), subgrammars.clone()))
            } else { None }
        ).next().unwrap();
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
                Terminal::Num(i) => prod_rules.push(Node::Constant(i)),
                Terminal::Var(v) => {
                    prod_rules.push(Node::Var(prod_rules.len()));
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

                // TODO
                // "mod" => prod_rules.push(Node::Mod([0, 0])),
                // "abs" => prod_rules.push(Node::Abs([0])),
                // "=" => prod_rules.push(Node::Ite([0, 0, 0])),
                // >, >=, <=

                "ite" => prod_rules.push(Node::Ite([0, 0, 0])),
                "<" => prod_rules.push(Node::Lt([0, 0])),
                _ => {},
            }
        }
    }

    SygusProblemAndOracle {
        progname,
        vars,
        constraint,
        prod_rules: prod_rules.into(),
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
        let mut query = String::new();
        for (var, val2) in self.vars.iter().zip(sigma.iter()) {
            let val2 = show_val(val2);
            query.push_str(&format!("(define-fun {var} () Int {val2})"));
        }
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let val = show_val(val);
        query.push_str(&format!(") Int {val})\n"));
        let constr = &self.constraint;
        query.push_str(&format!("(assert {constr})\n"));
        query.push_str("(check-sat)\n");

        let config = z3::Config::new();
        let ctxt = z3::Context::new(&config);
        let mut solver = z3::Solver::new(&ctxt);
        solver.from_string(query);

        solver.check() == z3::SatResult::Sat
    }
}

impl Oracle for SygusProblemAndOracle {
    fn verify(&self, term: &Term) -> Option<Sigma> {
        let mut query = String::new();
        for var in self.vars.iter() {
            query.push_str(&format!("(declare-var {var} Int)"));
        }
        let progname = &self.progname;

        query.push_str(&format!("(define-fun {progname} ("));
        for var in self.vars.iter() {
            query.push_str(&format!("({var} Int) "));
        }
        let term = term_to_z3(term.elems.len()-1, term, &self.vars);
        query.push_str(&format!(") Int {term})\n"));
        let constr = &self.constraint;
        query.push_str(&format!("(assert (not {constr}))\n"));

        let config = z3::Config::new();
        let ctxt = z3::Context::new(&config);
        let mut solver = z3::Solver::new(&ctxt);
        solver.from_string(query);

        if solver.check() == z3::SatResult::Sat {
            let ce = solver.get_model().unwrap();
            let mut sigma = Sigma::new();
            for var in &self.vars {
                let z3var = z3::ast::Int::from_str(&ctxt, var).unwrap();
                let z3val = ce.eval(&z3var, true); // TODO model completion?
                sigma.push(Value::Int(z3val.unwrap().as_i64().unwrap()));
            }
            return Some(sigma);
        } else { None }
    }
}

fn term_to_z3(i: usize, t: &Term, vars: &[String]) -> String {
    match &t.elems[i] {
        Node::Var(v) => vars[*v].clone(),

        &Node::Add([x, y]) => format!("(+ {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars)),
        &Node::Sub([x, y]) => format!("(- {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars)),
        &Node::Mul([x, y]) => format!("(* {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars)),
        &Node::Div([x, y]) => format!("(div {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars)),

        &Node::Ite([x, y, z]) => format!("(ite {} {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars), term_to_z3(z, t, vars)),
        &Node::Lt([x, y]) => format!("(< {} {})", term_to_z3(x, t, vars), term_to_z3(y, t, vars)),

        Node::Constant(i) => format!("{i}"),
    }
}

