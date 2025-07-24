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

fn add_node<'a, P: Problem>(node: Node, ctxt: &mut Ctxt<'a, P>) -> Id {
    let vals = vals(&node, ctxt);
    if let Some(&i) = ctxt.vals_lookup.get(&vals) {
        let newsize = minsize(&node, ctxt);
        let c = ctxt.classes.get_mut(i).unwrap();
        if newsize < c.size {
            c.size = newsize;
            // TODO upwards merge!
        }
        i
    } else {
        let i = ctxt.classes.len();
        ctxt.classes.push(Class {
            size: minsize(&node, ctxt),
            node,
            vals: vals.clone(),
        });
        ctxt.vals_lookup.insert(vals, i);
        i
    }
}

fn vals<'a, P: Problem>(node: &Node, ctxt: &Ctxt<'a, P>) -> Box<[Value]> {
    ctxt.sigmas.iter().enumerate().map(|(i, sigma)| {
        let f = |id: Id| ctxt.classes[id].vals[i].clone();
        eval_node(node, sigma, &f)
    }).collect::<Box<[_]>>()
}

fn minsize<'a, P: Problem>(node: &Node, ctxt: &Ctxt<'a, P>) -> usize {
    node.children().iter().map(|x| ctxt.classes[*x].size).sum::<usize>() + 1
}
