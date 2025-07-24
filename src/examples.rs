use crate::*;

pub fn enumerated<F: Fn(&Sigma, &Value) -> bool>(num_vars: usize, f: &F) -> (impl Problem, impl Oracle) {
    struct EnumeratedProblem<'f, F: Fn(&Sigma, &Value) -> bool> {
        num_vars: usize,
        f: &'f F,
    }

    struct EnumeratedOracle<'f, F: Fn(&Sigma, &Value) -> bool> {
        sigmas: Vec<Sigma>,
        f: &'f F,
    }

    impl<'f, F: Fn(&Sigma, &Value) -> bool> Problem for EnumeratedProblem<'f, F> {
        fn num_vars(&self) -> usize { self.num_vars }
        fn sat(&self, val: &Value, sigma: &Sigma) -> bool {
            (self.f)(sigma, val)
        }
    }

    impl<'f, F: Fn(&Sigma, &Value) -> bool> Oracle for EnumeratedOracle<'f, F> {
        fn verify(&self, term: &RecExpr<Term>) -> Option<Sigma> {
            for sigma in &self.sigmas {
                let v = eval_term(term, sigma);
                if !(self.f)(sigma, &v) {
                    return Some(sigma.clone());
                }
            }
            None
        }
    }

    let p = EnumeratedProblem {
        num_vars,
        f,
    };

    let o = EnumeratedOracle {
        sigmas: sigmas(0, num_vars),
        f,
    };

    (p, o)
}

fn sigmas(i: usize, num_vars: usize) -> Vec<Sigma> {
    if i == num_vars {
        return vec![Sigma::new()];
    }

    let mut outs = Vec::new();
    for rest in sigmas(i+1, num_vars) {
        for x in 0..num_vars {
            let mut sigma = Sigma::new();
            sigma.push(Value::Int(x as _));
            sigma.extend(rest.clone());
            outs.push(sigma);
        }
    }
    outs
}

fn vmax(v1: Value, v2: Value) -> Value {
    match (v1, v2) {
        (Value::Int(v1), Value::Int(v2)) => Value::Int(v1.max(v2)),
        _ => panic!(),
    }
}

pub fn max_n(n: usize) -> (impl Problem, impl Oracle) {
    assert!(n > 0);

    enumerated(n, &|sigma: &Sigma, v: &Value| -> bool {
        *v == sigma.iter().cloned().fold(Value::Int(0), vmax)
    })
}
