use crate::*;

pub struct MySynth;

type Score = usize;
type PrioQueue = BinaryHeap<WithOrd<Id, Score>>;

fn heuristic(info: &Info, sigmas: &[Sigma], problem: &impl Problem) -> Score {
    let counter = satcount(info, sigmas, problem);

    const A: usize = 1;
    const B: usize = 1;

    (counter + A) / (info.min_size + B)
}

fn satcount(info: &Info, sigmas: &[Sigma], problem: &impl Problem) -> usize {
    let vals = info.vals.iter();
    let sigmas = sigmas.iter();
    let it = vals.zip(sigmas);
    it.filter(|(val, sigma)| problem.sat(val, sigma))
      .count()
}

impl Synth for MySynth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> RecExpr<Term> {
        let mut g = G::new(ComputeValue {
            sigmas: sigmas.iter().cloned().collect(),
            veccons: Default::default(),
        });

        // queue contains all the integer typed classes.
        let mut queue: PrioQueue = BinaryHeap::new();

        for x in 0..problem.num_vars() {
            add(Term::Var(x), &mut g, sigmas, problem, &mut queue);
        }

        loop {
            let WithOrd(i, _) = queue.pop().unwrap();
            if satcount(&g[i].data, sigmas, problem) == sigmas.len() {
                let e = Extractor::new(&g, AstSize);
                let (_, t) = e.find_best(i);
                return t;
            }
            grow(i, &mut g, sigmas, problem, &mut queue);
        }
    }
}

fn grow(id: Id, g: &mut G, sigmas: &[Sigma], problem: &impl Problem, queue: &mut PrioQueue) {
    if g[id].data.ty != Ty::Int { return; }

    let vars: Vec<Id> = (0..problem.num_vars()).map(|x| g.add(Term::Var(x))).collect();
    for &v in &vars {
        add(Term::Add([id, v]), g, sigmas, problem, queue);
        add(Term::Add([v, id]), g, sigmas, problem, queue);

        add(Term::Sub([id, v]), g, sigmas, problem, queue);
        add(Term::Sub([v, id]), g, sigmas, problem, queue);

        add(Term::Mul([id, v]), g, sigmas, problem, queue);
        add(Term::Mul([v, id]), g, sigmas, problem, queue);

        add(Term::Div([id, v]), g, sigmas, problem, queue);
        add(Term::Div([v, id]), g, sigmas, problem, queue);

        for &v1 in &vars {
            for &v2 in &vars {
                let cond = g.add(Term::Lt([id, v]));
                add(Term::Ite([cond, v1, v2]), g, sigmas, problem, queue);

                let cond = g.add(Term::Lt([v, id]));
                add(Term::Ite([cond, v1, v2]), g, sigmas, problem, queue);

                let cond = g.add(Term::Lt([v, v1]));
                add(Term::Ite([cond, id, v2]), g, sigmas, problem, queue);

                let cond = g.add(Term::Lt([v, v1]));
                add(Term::Ite([cond, v2, id]), g, sigmas, problem, queue);
            }
        }
    }
}

fn add(term: Term, g: &mut G, sigmas: &[Sigma], problem: &impl Problem, queue: &mut PrioQueue) {
    let i = g.add(term);
    let h = heuristic(&g[i].data, sigmas, problem);
    queue.push(WithOrd(i, h));
}
