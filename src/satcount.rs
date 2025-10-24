use crate::*;

pub fn satcount2(nt: usize, id: Id, ctxt: &mut Ctxt) -> usize {
    if ctxt.problem.rettype != ctxt.problem.synth_fun.ret {
        return 0
    }

    let vals = &ctxt.classes[nt][id].vals;

    let mut sum = 0;

    for (big_sigma, indices) in ctxt.big_sigmas.iter().zip(ctxt.sigma_indices.iter()) {
        // This is a huge sigma. It's a
        // - big sigma (all variables from the constraints), plus
        // - one variable per invocation of the synthfun

        let mut sigma = big_sigma.clone();
        for i in indices {
            sigma.push(vals[*i].clone());
        }
        let v = eval_term(&ctxt.problem.constraint, &sigma);
        if let Some(Value::Bool(true)) = v {
            sum += 1;
        }
    }
    sum
}
