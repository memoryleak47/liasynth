use crate::*;

pub fn enumerated<F: Fn(&Sigma, &Value) -> bool>(num_vars: usize, maxval: usize, constants: &[Int], f: &F) -> (impl Problem, impl Oracle) {
    struct EnumeratedProblem<'f, F: Fn(&Sigma, &Value) -> bool> {
        num_vars: usize,
        constants: Box<[Int]>,
        f: &'f F,
    }

    struct EnumeratedOracle<'f, F: Fn(&Sigma, &Value) -> bool> {
        sigmas: Vec<Sigma>,
        f: &'f F,
    }

    impl<'f, F: Fn(&Sigma, &Value) -> bool> Problem for EnumeratedProblem<'f, F> {
        fn num_vars(&self) -> usize { self.num_vars }
        fn constants(&self) -> &[Int] { &*self.constants }
        fn sat(&self, val: &Value, sigma: &Sigma) -> bool {
            (self.f)(sigma, val)
        }
    }

    impl<'f, F: Fn(&Sigma, &Value) -> bool> Oracle for EnumeratedOracle<'f, F> {
        fn verify(&self, term: &Term) -> Option<Sigma> {
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
        constants: constants.iter().copied().collect(),
        f,
    };

    let o = EnumeratedOracle {
        sigmas: sigmas(0, num_vars, maxval),
        f,
    };

    (p, o)
}

fn sigmas(i: usize, num_vars: usize, maxval: usize) -> Vec<Sigma> {
    if i == num_vars {
        return vec![Sigma::new()];
    }

    let mut outs = Vec::new();
    for rest in sigmas(i+1, num_vars, maxval) {
        for x in 0..=maxval {
            for b in [true, false] {
                let mut sigma = Sigma::new();
                let x = x as i64;
                let x = if b { x } else { -x };
                sigma.push(Value::Int(x as _));
                sigma.extend(rest.clone());
                outs.push(sigma);
            }
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

    enumerated(n, 5, &[], &|sigma: &Sigma, v: &Value| -> bool {
        *v == sigma.iter().cloned().fold(Value::Int(Int::MIN), vmax)
    })
}

pub fn suc_x() -> (impl Problem, impl Oracle) {
    enumerated(1, 5, &[], &|sigma: &Sigma, v: &Value| -> bool {
        match (v, &sigma[0]) {
            (_, Value::Int(0)) => true,
            (Value::Int(l), Value::Int(r)) => *l == r+1,
            _ => false,
        }
    })
}

pub fn x_lt_y() -> (impl Problem, impl Oracle) {
    enumerated(2, 5, &[], &|sigma: &Sigma, v: &Value| -> bool {
        match sigma[..] {
            [Value::Int(x), Value::Int(y)] => *v == Value::Bool(x < y),
            _ => false,
        }
    })
}

pub fn x_plus_19() -> (impl Problem, impl Oracle) {
    enumerated(2, 5, &[19], &|sigma: &Sigma, v: &Value| -> bool {
        match sigma[..] {
            [Value::Int(x), _] => *v == Value::Int(x+19),
            _ => false,
        }
    })
}

pub fn qm_neg_eq_2() -> (impl Problem, impl Oracle) {
    enumerated(2, 5, &[0, 1], &|sigma: &Sigma, v: &Value| -> bool {
        match sigma[..] {
            [Value::Int(x), Value::Int(y)] => *v == (if x <= 0 && y <= 0 { Value::Int(1) } else { Value::Int(0) }),
            _ => false,
        }
    })
}
