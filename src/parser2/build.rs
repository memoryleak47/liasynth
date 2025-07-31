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
            "declare-var" => handle_declare_var(&l[1..], &mut synth),
            "constraint" => handle_constraint(&l[1..], &mut synth),
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

fn as_ty(s: &str) -> Ty {
    match s {
        "Int" => Ty::Int,
        "Bool" => Ty::Bool,
        _ => panic!(),
    }
}

fn handle_synth_fun(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(name), SExpr::List(args_), SExpr::Ident(ret), SExpr::List(nonterminals), SExpr::List(nonterminal_defs)] = l else { panic!() };

    let mut args = IndexMap::new();
    for a in args_ {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(l), SExpr::Ident(r)] = &v[..] else { panic!() };
        args.insert(l.clone(), as_ty(r));
    }

    synth.synthfuns.insert(name.clone(), SynthFun {
        ret: as_ty(ret),
        args,
        nonterminals: IndexMap::default(), // TODO
        nonterminal_defs: IndexMap::default(), // TODO
    });
}

fn handle_declare_var(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(s), SExpr::Ident(ty)] = l else { panic!() };
    synth.declared_vars.insert(s.to_string(), as_ty(ty));
}

fn handle_constraint(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::List(l)] = l else { panic!() };
    // TODO add constraint.
}
