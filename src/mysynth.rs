use crate::*;

const DEBUG: bool = true;

pub struct MySynth;

type Score = usize;
type PrioQueue = BinaryHeap<WithOrd<Id, Score>>;

fn heuristic(info: &Info, sigmas: &[Sigma], problem: &impl Problem) -> Score {
    let counter = satcount(info, sigmas, problem);

    const A: usize = 1;
    const B: usize = 5;

    (1000 * (counter + A)) / (info.min_size + B)
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
            add(Term::Var(Var(x)), &mut g, sigmas, problem, &mut queue);
        }

        loop {
            let WithOrd(i, score) = queue.pop().unwrap();
            let cnt = satcount(&g[i].data, sigmas, problem);
            let b = cnt == sigmas.len();
            if b || DEBUG {
                let e = Extractor::new(&g, AstSize);
                let (ast_size, t) = e.find_best(i);
                if DEBUG {
                    let sigs = sigmas.len();
                    let ast2 = g[i].data.min_size;
                    println!("[{sigs}] sc={score} sat={cnt} ast1={ast_size} ast2={ast2} {t}");
                }
                if b {
                    return t;
                }
            }
            grow(i, &mut g, sigmas, problem, &mut queue);
        }
    }
}

fn grow(id: Id, g: &mut G, sigmas: &[Sigma], problem: &impl Problem, queue: &mut PrioQueue) {
    assert!(g[id].data.ty == Ty::Int);

    // Why does this happen?
    if g[id].data.already_grown { return; }

    let vars: Vec<Id> = (0..problem.num_vars()).map(|x| g.add(Term::Var(Var(x)))).collect();
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

    let mut info = g[id].data.clone();
    info.already_grown = true;
    g.set_analysis_data(id, info);
}

fn add(term: Term, g: &mut G, sigmas: &[Sigma], problem: &impl Problem, queue: &mut PrioQueue) {
    let i = g.add(term);
    let info = &g[i].data;

    if info.ty == Ty::Int && !info.already_grown {
        let h = heuristic(&g[i].data, sigmas, problem);
        queue.push(WithOrd(i, h));
    }
}
