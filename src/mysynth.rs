use crate::*;

const DEBUG: bool = true;

pub struct MySynth;

type Score = usize;
type PrioQueue = BinaryHeap<WithOrd<Id, Score>>;

struct Ctxt<'a, P: Problem> {
    queue: PrioQueue,
    sigmas: &'a [Sigma],
    problem: &'a P,
    g: G,
}

fn heuristic<'a, P: Problem>(info: &Info, ctxt: &Ctxt<'a, P>) -> Score {
    let counter = satcount(info, ctxt);

    let mut a = 100000;
    for _ in counter..ctxt.sigmas.len() {
        a /= 2;
    }

    a / (info.min_size + 5)
}

fn satcount<'a, P: Problem>(info: &Info, ctxt: &Ctxt<'a, P>) -> usize {
    let vals = info.vals.iter();
    let it = vals.zip(ctxt.sigmas);
    it.filter(|(val, sigma)| ctxt.problem.sat(val, sigma))
      .count()
}

impl Synth for MySynth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> RecExpr<Term> {
        let g = G::new(ComputeValue {
            sigmas: sigmas.iter().cloned().collect(),
            veccons: Default::default(),
        });
        let mut ctxt = Ctxt {
            problem,
            sigmas,
            g,
            queue: Default::default(),
        };
        run(&mut ctxt)
    }
}

fn run<'a, P: Problem>(ctxt: &mut Ctxt<'a, P>) -> RecExpr<Term> {
    for x in 0..ctxt.problem.num_vars() {
        add(Term::Var(Var(x)), ctxt);
    }

    loop {
        let WithOrd(i, score) = ctxt.queue.pop().unwrap();
        let cnt = satcount(&ctxt.g[i].data, ctxt);
        let b = cnt == ctxt.sigmas.len();
        if b || DEBUG {
            let e = Extractor::new(&ctxt.g, AstSize);
            let (ast_size, t) = e.find_best(i);
            if DEBUG {
                let sigs = ctxt.sigmas.len();
                let ast2 = ctxt.g[i].data.min_size;
                println!("[{sigs}] sc={score} sat={cnt} ast1={ast_size} ast2={ast2} {t}");
            }
            if b {
                return t;
            }
        }
        grow(i, ctxt);
    }
}

fn grow<'a, P: Problem>(id: Id, ctxt: &mut Ctxt<'a, P>) {
    assert!(ctxt.g[id].data.ty == Ty::Int);

    // Why does this happen?
    if ctxt.g[id].data.already_grown { return; }

    let vars: Vec<Id> = (0..ctxt.problem.num_vars()).map(|x| ctxt.g.add(Term::Var(Var(x)))).collect();
    for &v in &vars {
        add(Term::Add([id, v]), ctxt);
        add(Term::Add([v, id]), ctxt);

        add(Term::Sub([id, v]), ctxt);
        add(Term::Sub([v, id]), ctxt);

        add(Term::Mul([id, v]), ctxt);
        add(Term::Mul([v, id]), ctxt);

        add(Term::Div([id, v]), ctxt);
        add(Term::Div([v, id]), ctxt);

        for &v1 in &vars {
            for &v2 in &vars {
                let cond = ctxt.g.add(Term::Lt([id, v]));
                add(Term::Ite([cond, v1, v2]), ctxt);

                let cond = ctxt.g.add(Term::Lt([v, id]));
                add(Term::Ite([cond, v1, v2]), ctxt);

                let cond = ctxt.g.add(Term::Lt([v, v1]));
                add(Term::Ite([cond, id, v2]), ctxt);

                let cond = ctxt.g.add(Term::Lt([v, v1]));
                add(Term::Ite([cond, v2, id]), ctxt);
            }
        }
    }

    let mut info = ctxt.g[id].data.clone();
    info.already_grown = true;
    ctxt.g.set_analysis_data(id, info);
}

fn add<'a, P: Problem>(term: Term, ctxt: &mut Ctxt<'a, P>) {
    let i = ctxt.g.add(term);
    let info = &ctxt.g[i].data;

    if info.ty == Ty::Int && !info.already_grown {
        let h = heuristic(&ctxt.g[i].data, ctxt);
        ctxt.queue.push(WithOrd(i, h));
    }
}
