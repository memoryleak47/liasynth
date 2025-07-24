use crate::*;

pub struct MySynth;

pub type Score = usize;

fn heuristic(info: &Info, sigmas: &[Sigma], problem: &impl Problem) -> Score {
    let counter = info.vals.iter().zip(sigmas.iter()).filter(|(val, sigma)|
        problem.sat(val, sigma)).count();

    const A: usize = 1;
    const B: usize = 1;

    (counter + A) / (info.min_size + B)
}

impl Synth for MySynth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> Term {
        let mut g = G::new(ComputeValue {
            sigmas: sigmas.iter().cloned().collect(),
            veccons: Default::default(),
        });

        let mut queue: BinaryHeap<WithOrd<Id, Score>> = BinaryHeap::new();

        for x in 0..problem.num_vars() {
            let i = g.add(Term::Var(x));
            let h = heuristic(&g[i].data, sigmas, problem);
            queue.push(WithOrd(i, h));
        }

        loop {
            let WithOrd(i, _) = queue.pop().unwrap();
            grow(&mut g, i);
        }
    }
}

fn grow(g: &mut G, id: Id) {
    // for each production rule add a term, where id is one child, and all the other children are variables.
    todo!()
}
