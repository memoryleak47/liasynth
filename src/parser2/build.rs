use crate::*;
use crate::parser2::*;

pub fn build_synth(exprs: Vec<SExpr>) -> SynthProblem {
    let mut synth = SynthProblem::default();
    for e in exprs {
        let SExpr::List(l) = e else { panic!() };
        let SExpr::Ident(a) = &l[0] else { panic!() };
        match &**a {
            "set-logic" => handle_set_logic(&l[1..], &mut synth),
            "check-synth" => handle_check_synth(&l[1..], &mut synth),
            "synth-fun" => handle_synth_fun(&l[1..], &mut synth),
            f => panic!("unknown SynthProblem command {f}"),
        }
    }
    synth
}

fn handle_set_logic(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(s)] = l else { panic!() };
    match &**s {
        "LIA" => { synth.logic = Some(Logic::LIA); },
        s => panic!("unsupported logic {s}"),
    }
}

fn handle_check_synth(l: &[SExpr], synth: &mut SynthProblem) {
    synth.check_synth = true;
}

fn handle_synth_fun(l: &[SExpr], synth: &mut SynthProblem) {
    todo!()
}


