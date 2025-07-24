use crate::*;

pub struct MySynth;

type Score = usize;
type Queue = BinaryHeap<WithOrd<Id, Score>>;

struct Ctxt<'a, P> {
    queue: Queue,
    sigmas: &'a [Sigma],
    problem: &'a P,

    vals_lookup: Map<Box<[Value]>, Id>,
    classes: Vec<Class>,
}

struct Class {
    node: Node,
    size: usize,
    vals: Box<[Value]>,
}

fn run<'a, P>(ctxt: &mut Ctxt<P>) -> Term {
    todo!()
}

impl Synth for MySynth {
    fn synth(&mut self, problem: &impl Problem, sigmas: &[Sigma]) -> Term {
        run(&mut Ctxt {
            queue: Default::default(),
            sigmas,
            problem,
            vals_lookup: Default::default(),
            classes: Vec::new(),
        })
    }
}
