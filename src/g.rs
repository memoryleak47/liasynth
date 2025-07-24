use crate::*;

pub type G = EGraph<Term, ComputeValue>;

#[derive(Default)]
pub struct ComputeValue {
    pub sigmas: Vec<Sigma>,
    pub veccons: Map<Vec<Value>, Id>,
}

#[derive(Debug)]
pub struct Info {
    pub vals: Vec<Value>,
    pub min_size: usize,
}

impl Analysis<Term> for ComputeValue {
    type Data = Info;

    fn make(eg: &mut G, enode: &Term) -> Info {
        let vals = eg.analysis.sigmas.iter().enumerate().map(|(i, sigma)|
                    eval_step(enode, sigma, &|c| eg[c].data.vals[i].clone())
                ).collect();
        let min_size = enode.children().iter().map(|c| eg[*c].data.min_size).sum::<usize>() + 1;
        Info { vals, min_size }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        assert!(&a.vals == &b.vals);
        let a_size = a.min_size;
        let b_size = b.min_size;
        a.min_size = a_size.min(b_size);
        DidMerge(a_size > b_size, b_size > a_size)
    }

    fn modify(eg: &mut G, i: Id) {
        let data = &eg[i].data;
        if let Some(x) = eg.analysis.veccons.get(&data.vals) {
            if eg.find(i) != eg.find(*x) {
                eg.union(*x, i);
            }
        } else {
            eg.analysis.veccons.insert(data.vals.clone(), i);
        }
    }
}
