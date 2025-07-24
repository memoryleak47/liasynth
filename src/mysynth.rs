use crate::*;

pub struct MySynth;

type Score = usize;
type PrioQueue = BinaryHeap<WithOrd<Term, Score>>;

struct Ctxt<'a, P: Problem> {
    queue: PrioQueue,
    sigmas: &'a [Sigma],
    problem: &'a P,
    g: G,
}

fn heuristic<'a, P: Problem>(node: &Term, ctxt: &Ctxt<'a, P>) -> Score {
    let satcount = satcount(node, ctxt);
    let minsize = minsize(node, ctxt);

    let mut a = 100000;
    for _ in satcount..ctxt.sigmas.len() {
        a /= 2;
    }

    a / (minsize + 5)
}

fn satcount<'a, P: Problem>(node: &Term, ctxt: &Ctxt<'a, P>) -> usize {
    let vals = vals(node, ctxt);
    let it = vals.iter().zip(ctxt.sigmas);
    it.filter(|(val, sigma)| ctxt.problem.sat(val, sigma))
      .count()
}

fn minsize<'a, P: Problem>(node: &Term, ctxt: &Ctxt<'a, P>) -> usize {
    node.children().into_iter().map(|x| ctxt.g[*x].data.min_size).sum::<usize>() + 1
}

fn vals<'a, P: Problem>(node: &Term, ctxt: &Ctxt<'a, P>) -> Vec<Value> {
    ctxt.sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |id: Id| ctxt.g[id].data.vals[i].clone();
        eval_step(node, sigma, &f)
    }).collect()
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
        enqueue(Term::Var(Var(x)), ctxt);
    }

    loop {
        let WithOrd(node, _score) = ctxt.queue.pop().unwrap();
        let satcount = satcount(&node, ctxt);
        let i = ctxt.g.add(node);

        if satcount == ctxt.sigmas.len() {
            let e = Extractor::new(&ctxt.g, AstSize);
            let (_, t) = e.find_best(i);
            return t;
        }

        on_add(i, ctxt);
    }
}

fn on_add<'a, P: Problem>(id: Id, ctxt: &mut Ctxt<'a, P>) {
    let mut class_b = Vec::new();
    let mut class_i = Vec::new();
    for c in ctxt.g.classes() {
        if c.data.ty == Ty::Int {
            class_i.push(c.id);
        } else {
            class_b.push(c.id);
        }
    }

    if ctxt.g[id].data.ty == Ty::Int {
        for &x in &class_i {
            enqueue(Term::Add([id, x]), ctxt);
            enqueue(Term::Add([x, id]), ctxt);

            enqueue(Term::Sub([id, x]), ctxt);
            enqueue(Term::Sub([x, id]), ctxt);

            enqueue(Term::Mul([id, x]), ctxt);
            enqueue(Term::Mul([x, id]), ctxt);

            enqueue(Term::Div([id, x]), ctxt);
            enqueue(Term::Div([x, id]), ctxt);

            enqueue(Term::Lt([id, x]), ctxt);
            enqueue(Term::Lt([x, id]), ctxt);

            for &cond in &class_b {
                enqueue(Term::Ite([cond, id, x]), ctxt);
                enqueue(Term::Ite([cond, x, id]), ctxt);
            }
        }
    } else {
        for &x in &class_i {
            for &y in &class_i {
                enqueue(Term::Ite([id, x, y]), ctxt);
            }
        }
    }
}

fn enqueue<'a, P: Problem>(term: Term, ctxt: &mut Ctxt<'a, P>) {
    let vals = vals(&term, ctxt);
    if ctxt.g.analysis.veccons.contains_key(&vals) { return; }

    let h = heuristic(&term, ctxt);
    ctxt.queue.push(WithOrd(term, h));
}
