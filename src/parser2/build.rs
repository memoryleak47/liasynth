use crate::*;
use crate::parser2::{Expr, DefinedFun, *};

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
            "define-fun" => handle_define_fun(&l[1..], &mut synth),
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

fn as_rule(s: &SExpr, nonterminals: &IndexMap<String, Ty>) -> ProdRule {
    match s {
        SExpr::Ident(id) if nonterminals.contains_key(id) => ProdRule::NonTerminal(id.clone()),
        SExpr::Ident(id) => ProdRule::Const(id.clone()),
        SExpr::List(l) => {
            let [SExpr::Ident(op), rst@..] = &l[..] else { panic!() };
            let rst = rst.iter().map(|x| as_rule(x, nonterminals)).collect();
            ProdRule::Op(op.clone(), rst)
        }
    }
}

fn as_expr(s: &SExpr) -> Expr {
    match s {
        SExpr::Ident(id) => Expr::Const(id.clone()),
        SExpr::List(l) => {
            let [SExpr::Ident(op), rst@..] = &l[..] else { panic!("{:?}", l) };
            if op == "let" {
                let [SExpr::List(bindings_), expr] = rst else { panic!() };
                let mut bindings = IndexMap::new();
                for b in bindings_ {
                    let SExpr::List(b) = b else { panic!() };
                    let [SExpr::Ident(var), ex] = &**b else { panic!() };
                    let ex = as_expr(ex);
                    bindings.insert(var.clone(), ex);
                }
                let expr = as_expr(expr);
                Expr::Let(bindings, Box::new(expr))
            } else {
                let rst = rst.iter().map(|x| as_expr(x)).collect();
                Expr::Op(op.clone(), rst)
            }
        }
    }
}

fn handle_synth_fun(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(name), SExpr::List(args_), SExpr::Ident(ret), SExpr::List(nonterminals_), SExpr::List(nonterminal_defs_)] = l else { panic!() };

    let mut args = IndexMap::new();
    for a in args_ {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(l), SExpr::Ident(r)] = &v[..] else { panic!() };
        args.insert(l.clone(), as_ty(r));
    }

    let mut nonterminals = IndexMap::new();
    for a in nonterminals_ {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(name), SExpr::Ident(ty)] = &v[..] else { panic!() };
        nonterminals.insert(name.clone(), as_ty(ty));
    }

    let mut nonterminal_defs = IndexMap::new();
    for a in nonterminal_defs_ {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(name), SExpr::Ident(ty), SExpr::List(rules)] = &v[..] else { panic!() };
        let rules = rules.iter().map(|x| as_rule(x, &nonterminals)).collect();
        nonterminal_defs.insert(name.clone(), NonterminalDef {
            ty: as_ty(ty),
            rules,
        });
    }

    synth.synthfuns.insert(name.clone(), SynthFun {
        ret: as_ty(ret),
        args,
        nonterminals,
        nonterminal_defs,
    });
}

fn handle_declare_var(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(s), SExpr::Ident(ty)] = l else { panic!() };
    synth.declared_vars.insert(s.to_string(), as_ty(ty));
}

fn handle_define_fun(l: &[SExpr], synth: &mut SynthProblem) {
    let [SExpr::Ident(name), SExpr::List(args_), SExpr::Ident(ret), expr] = l else { panic!() };

    let mut args = IndexMap::new();
    for a in args_ {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(var), SExpr::Ident(ty)] = &v[..] else { panic!() };
        args.insert(var.to_string(), as_ty(ty));
    }

    let fun = DefinedFun {
        args,
        expr: as_expr(expr),
        ret: as_ty(ret),
    };
    synth.defined_funs.insert(name.clone(), fun);
}

fn handle_constraint(l: &[SExpr], synth: &mut SynthProblem) {
    let [e] = &l[..] else { panic!() };
    synth.constraints.push(as_expr(e));
}
