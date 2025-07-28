use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    vars: Vec<String>,

    // These strings will be interpreted by Z3.
    constraints: Box<[String]>,

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
    let (vars, subgrammars): (Vec<(String, Type)>, Vec<SubGrammar>) =
        exprs.iter().filter_map(|x|
            if let SyGuSExpr::SynthFun(_, vars, _, _, subgrammars) = x {
                Some((vars.clone(), subgrammars.clone()))
            } else { None }
        ).next().unwrap();
    let vars: Vec<String> = vars.into_iter().map(|(x, _)| x).collect();

    let constraints: Box<[String]> = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(prettyprint(&e))
        } else { None }
    ).collect();

    let mut prod_rules = Vec::new();
    for g in subgrammars {
        for t in g.terminals {
            match t {
                Terminal::Num(i) => prod_rules.push(Node::Constant(i)),
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
        vars,
        constraints,
        prod_rules: prod_rules.into(),
    }
}

impl Problem for SygusProblemAndOracle {
    fn num_vars(&self) -> usize { todo!() }
    fn constants(&self) -> &[Int] { todo!() }
    fn check_node(&self, n: &Node) -> bool { todo!() }
    fn sat(&self, val: &Value, sigma: &Sigma) -> bool { todo!() }
}

impl Oracle for SygusProblemAndOracle {
    fn verify(&self, term: &Term) -> Option<Sigma> { todo!() }
}
