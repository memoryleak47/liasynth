use indexmap::IndexMap;
use std::fmt::*;
use crate::Ty;

mod sexpr;
use sexpr::*;

mod build;
use build::*;

#[derive(Debug)]
struct NonterminalDef {
    ty: Ty,
    rules: Vec<ProdRule>,
}

#[derive(Debug)]
struct SynthFun {
    name: String,
    args: IndexMap<String, Ty>,
    ret: Ty,
    nonterminals: IndexMap<String, Ty>,
    nonterminal_defs: IndexMap<String, NonterminalDef>,
}

#[derive(Debug)]
enum ProdRule {
    NonTerminal(String),
    Const(String),
    Op(String, Vec<ProdRule>),
}

#[derive(Debug)]
struct Expr {
    op: String,
    children: Vec<Expr>,
}

#[derive(Debug)]
enum Logic {
    LIA,
    BitVec,
}


#[derive(Debug)]
struct DeclaredVar {
    var: String,
    ty: Ty, // can really only be Int / Bool / BitVec.
}

#[derive(Debug)]
struct DefinedFun {
    name: String,
    ret: Ty,
    args: Vec<(String, Ty)>,
    expr: Expr,
}

#[derive(Debug, Default)]
pub struct SynthProblem {
    logic: Option<Logic>,
    synthfuns: Vec<SynthFun>,
    constraints: Vec<Expr>,
    defined_funs: Vec<DefinedFun>,
    declared_vars: Vec<DeclaredVar>,
    check_synth: bool,
}

pub fn parse_synth(s: &str) -> SynthProblem {
    let toks_src = tokenize(s);
    let mut toks = &*toks_src;

    let mut exprs = Vec::new();
    while toks.len() > 0 {
        let (expr, toks2) = assemble(&toks).unwrap();
        toks = toks2;
        exprs.push(expr)
    }
    assert!(toks.is_empty());
    build_synth(exprs)
}

