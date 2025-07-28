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

    let pao: SygusProblemAndOracle = todo!();

    (pao.clone(), pao)
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
