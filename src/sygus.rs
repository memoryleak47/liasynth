use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    // maps between the SyGuS named variables, and the
    // variable indices from our synthesizer.
    vars: Vec<String>,

    // These strings will be interpreted by Z3.
    constraints: Box<[String]>,

    constants: Box<[Int]>,
}

pub fn sygus_problem(f: &str) -> (impl Problem, impl Oracle) {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    let pao = build_sygus(parsed);

    (pao.clone(), pao)
}

fn build_sygus(exprs: Vec<SyGuSExpr>) -> SygusProblemAndOracle {
    let mut vars: Vec<(String, Type)> =
        exprs.iter().filter_map(|x|
            if let SyGuSExpr::SynthFun(_, vars, ..) = x {
                Some(vars.clone())
            } else { None }
        ).next().unwrap();
    let vars: Vec<String> = vars.into_iter().map(|(x, _)| x).collect();

    let constraints: Box<[_]> = exprs.iter().filter_map(|x|
        if let SyGuSExpr::Constraint(e) = x {
            Some(vars.clone())
        } else { None }
    ).collect();

    SygusProblemAndOracle {
        vars,
        constraints: todo!(),
        constants: todo!(),
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
