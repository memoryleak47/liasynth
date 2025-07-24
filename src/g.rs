use crate::*;

pub type G = EGraph<Term, ComputeValue>;

#[derive(Default)]
pub struct ComputeValue {
    sigmas: Vec<Sigma>,
    veccons: Map<Vec<Value>, Id>,
}

impl Analysis<Term> for ComputeValue {
    type Data = (Vec<Value>, bool); // (evaluated value, is_sat)

    fn make(eg: &mut G, enode: &Term) -> (Vec<Value>, bool) {
        let v = eg.analysis.sigmas.iter().enumerate().map(|(i, sigma)|
                    eval_step(enode, sigma, &|c| eg[c].data.0[i].clone())
                ).collect();
        (v, false)
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        assert!(&a.0 == &b.0);
        DidMerge(false, false)
    }

    fn modify(eg: &mut G, i: Id) {
        let data = &eg[i].data;
        if let Some(x) = eg.analysis.veccons.get(&data.0) {
            if eg.find(i) != eg.find(*x) {
                eg.union(*x, i);
            }
        } else {
            eg.analysis.veccons.insert(data.0.clone(), i);
        }
    }
}
