use crate::*;

#[derive(Clone)]
struct SygusProblemAndOracle {
    expr: Vec<SyGuSExpr>,
}

pub fn sygus_problem(f: &str) -> (impl Problem, impl Oracle) {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    let mut num_vars = 0;
    let vars: Vec<SyGuSExpr> = parsed.iter().filter_map(|x| match x {
        SyGuSExpr::SynthFun(_, vars, ..) => Some(vars.clone()),
        _ => None,
    }).next().unwrap();

    let pao = SygusProblemAndOracle {
        expr: parsed,
    };

    (pao.clone(), pao)
}

impl Problem for SygusProblemAndOracle {
    fn num_vars(&self) -> usize { todo!() }
    fn constants(&self) -> &[Int] { todo!() }
    fn sat(&self, val: &Value, sigma: &Sigma) -> bool { todo!() }
}

impl Oracle for SygusProblemAndOracle {
    fn verify(&self, term: &Term) -> Option<Sigma> { todo!() }
}
