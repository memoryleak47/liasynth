use crate::*;


#[derive(Clone)]
struct SygusProblemAndOracle {
    expr: Vec<SyGuSExpr>,
}

type SynthFun<'a> = (&'a str, &'a [SyGuSExpr], &'a Type, &'a [SyGuSExpr], &'a [SubGrammar]);

impl SygusProblemAndOracle {
    fn synthfun(&self) -> SynthFun<'_> {
        for x in self.expr.iter() {
            if let SyGuSExpr::SynthFun(a, b, c, d, e) = x {
                return (&*a, &*b, &*c, &*d, &*e);
            }
        }
        panic!()
    }
}

pub fn sygus_problem(f: &str) -> (impl Problem, impl Oracle) {
    let s = std::fs::read_to_string(f).unwrap();
    let (parsed, _) = parse_sygus(&s).unwrap();

    let pao = SygusProblemAndOracle {
        expr: parsed,
    };

    (pao.clone(), pao)
}

impl Problem for SygusProblemAndOracle {
    fn num_vars(&self) -> usize {
        let (_, vars, ..) = self.synthfun();
        vars.len()
    }

    fn constants(&self) -> &[Int] { todo!() }

    fn sat(&self, val: &Value, sigma: &Sigma) -> bool { todo!() }
}

impl Oracle for SygusProblemAndOracle {
    fn verify(&self, term: &Term) -> Option<Sigma> { todo!() }
}
