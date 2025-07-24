use crate::*;

pub type G = EGraph<Term, ComputeValue>;

#[derive(Default)]
pub struct ComputeValue {
    pub sigmas: Vec<Sigma>,
    pub veccons: Map<Vec<Value>, Id>,
}

#[derive(Debug, Clone)]
pub struct Info {
    pub vals: Vec<Value>,
    pub min_size: usize,
    pub ty: Ty,
    pub already_grown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Int,
    Bool,
}

impl Analysis<Term> for ComputeValue {
    type Data = Info;

    fn make(eg: &mut G, enode: &Term) -> Info {
        let vals: Vec<_> = eg.analysis.sigmas.iter().enumerate().map(|(i, sigma)|
                    eval_step(enode, sigma, &|c| eg[c].data.vals[i].clone())
                ).collect();
        let min_size = enode.children().iter().map(|c| eg[*c].data.min_size).sum::<usize>() + 1;
        let ty = vals.get(0).map(|x| match x {
            Value::Int(_) => Ty::Int,
            Value::Bool(_) => Ty::Bool,
        }).unwrap_or(Ty::Int);
        let already_grown = false;
        Info { vals, min_size, ty, already_grown }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        assert!(&a.vals == &b.vals);
        assert!(&a.ty == &b.ty);

        let a_changed = a.min_size > b.min_size;
        let b_changed = b.min_size > a.min_size;
        a.min_size = a.min_size.min(b.min_size);

        let final_grown = a.already_grown || b.already_grown;
        let a_changed = a_changed || (final_grown != a.already_grown);
        let b_changed = b_changed || (final_grown != b.already_grown);
        a.already_grown = final_grown;

        DidMerge(a_changed, b_changed)
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
