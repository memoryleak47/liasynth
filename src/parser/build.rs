use crate::*;
use crate::parser::*;
use itertools::Itertools;

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

// checks whether 'op' is an OP
fn valid_op(op: &str, arity: usize) -> Option<Node> {
    let v: Box<[Node]> = (0..arity).map(|i| Node::PlaceHolder(i, Ty::Int)).collect();  
    Node::parse(op, &v)
}

fn valid_prod(prod: &str, a: &Vec<GrammarTerm>, args: &IndexMap<String, Ty>) -> Option<Node> {
    let v: Box<[Node]> = a
        .iter()
        .map(|n|
            match n {
                GrammarTerm::NonTerminal(_, t) => {
                    Node::PlaceHolder(0, *t)
                },
                GrammarTerm::SynthArg(v, ty) => {
                    if let Some(idx) =  args.get_index_of(v) {
                        match &args[idx] {
                            Ty::Int => Node::VarInt(idx, *ty),
                            Ty::Bool => Node::VarBool(idx, *ty),
                            _ => panic!("should not happen")
                        }
                    } else {
                        panic!("that shouldnt happen")
                    }
                }
                _ => panic!("that shouldnt happen")
            }).collect();
    Node::parse_prod(prod, &v)
}

fn make_string(l: &SExpr, nonterms: &IndexMap<String, Ty>) -> String {
    match l {
        SExpr::Ident(s) => {
            if nonterms.contains_key(s) { "?".to_string() } else { s.to_string() }
        }
        SExpr::List(xs) => format!("({})", xs.iter().map(|x| make_string(x, nonterms)).join(" ")),
    }
}

fn get_rst(l: &SExpr, nonterms: &IndexMap<String, Ty>, args: &IndexMap<String, Ty>) -> Vec<GrammarTerm> {
    match l {
        SExpr::Ident(s) => {
            if nonterms.contains_key(s) {
                let nt = nonterms.get(s).unwrap();
                return vec![GrammarTerm::NonTerminal(s.clone(), *nt)] ; }
            else if args.contains_key(s) {
                let nt = args.get(s).unwrap();
                return vec![GrammarTerm::SynthArg(s.clone(), *nt)];
            }
            else { vec![] }
        }
        SExpr::List(xs) => xs.iter().flat_map(|x| get_rst(x, nonterms, args)).collect::<Vec<GrammarTerm>>()
    }
}

fn as_rule(nt: usize, s: &SExpr, nonterminals: &IndexMap<String, Ty>, args: &IndexMap<String, Ty>, defs: &IndexMap<String, DefinedFun>) -> GrammarTerm {
    match s {
        SExpr::Ident(id) => {
            if nonterminals.contains_key(id) {return GrammarTerm::NonTerminal(id.clone(), Ty::NonTerminal(nt)); }
            if let Ok(i) = id.parse::<Int>() { return GrammarTerm::ConstInt(i, Ty::NonTerminal(nt)); }
            if id == "true" { return GrammarTerm::ConstBool(true, Ty::NonTerminal(nt)); }
            if id == "false" { return GrammarTerm::ConstBool(false, Ty::NonTerminal(nt)); }
            if args.contains_key(id) { return GrammarTerm::SynthArg(id.clone(), Ty::NonTerminal(nt)); }

            panic!("unknown ident: {id}")
        },
        SExpr::List(l) => {

            let [SExpr::Ident(op), rst@..] = &l[..] else { panic!() };

            // special case for negative number constants:
            if let [SExpr::Ident(a)] = rst && op == "-" {
                if let Ok(i) = a.parse::<Int>() {
                    return GrammarTerm::ConstInt(-i, Ty::NonTerminal(nt));
                }
            }

            let s = format!("({})", l.iter().map(|x| make_string(x, nonterminals)).join(" "));

            if defs.contains_key(op) {
                let rst = rst.iter().map(|x| {
                    as_rule(nt, x, nonterminals, args, defs)
                }).collect();
                return GrammarTerm::DefinedFunCall(op.clone(), s, rst);
            }

            let s = format!("({})", l.iter().map(|x| make_string(x, nonterminals)).join(" "));
            let rst = l.iter().flat_map(|x| get_rst(x, nonterminals, args)).collect::<Vec<_>>();

            if valid_prod(&s, &rst, args).is_some() {
                return GrammarTerm::Op(s, rst);
            }

            panic!("unknown op: {s}")
        }
    }
}

fn as_expr(s: &SExpr, defined_funs: &IndexMap<String, DefinedFun>, synth_funs: &IndexMap<String, SynthFun>) -> Expr {
    match s {
        SExpr::Ident(id) => {
            if let Ok(i) = id.parse::<Int>() { return Expr::ConstInt(i); }
            if id == "true" { return Expr::ConstBool(true); }
            if id == "false" { return Expr::ConstBool(false); }
            Expr::Var(id.clone()) // TODO always correct?
        },
        SExpr::List(l) => {
            let [SExpr::Ident(op), rst@..] = &l[..] else { panic!("{:?}", l) };
            if op == "let" {
                let [SExpr::List(bindings_), expr] = rst else { panic!() };
                let mut bindings = IndexMap::new();
                for b in bindings_ {
                    let SExpr::List(b) = b else { panic!() };
                    let [SExpr::Ident(var), ex] = &**b else { panic!() };
                    let ex = as_expr(ex, defined_funs, synth_funs);
                    bindings.insert(var.clone(), ex);
                }
                let expr = as_expr(expr, defined_funs, synth_funs);
                Expr::Let(bindings, Box::new(expr))
            } else if valid_op(op, rst.len()).is_some() {
                let rst = rst.iter().map(|x| as_expr(x, defined_funs, synth_funs)).collect();
                Expr::Op(op.clone(), rst)
            } else if defined_funs.contains_key(op) {
                let rst = rst.iter().map(|x| as_expr(x, defined_funs, synth_funs)).collect();
                Expr::DefinedFunCall(op.clone(), rst)
            } else if synth_funs.contains_key(op) {
                let rst = rst.iter().map(|x| as_expr(x, defined_funs, synth_funs)).collect();
                Expr::SynthFunCall(op.clone(), rst)
            } else {
                panic!("invalid op: {op}")
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
    for (nt, a) in nonterminal_defs_.iter().enumerate() {
        let SExpr::List(v) = a else { panic!() };
        let [SExpr::Ident(name), SExpr::Ident(ty), SExpr::List(rules)] = &v[..] else { panic!() };
        let prod_rules = rules.iter().map(|x| as_rule(nt, x, &nonterminals, &args, &synth.defined_funs)).collect();
        nonterminal_defs.insert(name.clone(), NonterminalDef {
            ty: as_ty(ty),
            prod_rules,
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
        name: name.clone(),
        args,
        expr: as_expr(expr, &synth.defined_funs, &synth.synthfuns),
        ret: as_ty(ret),
    };
    synth.defined_funs.insert(name.clone(), fun);
}

fn handle_constraint(l: &[SExpr], synth: &mut SynthProblem) {
    let [e] = &l[..] else { panic!() };
    synth.constraints.push(as_expr(e, &synth.defined_funs, &synth.synthfuns));
}
