use indexmap::IndexMap;
use std::fmt::*;
use crate::Ty;

mod sexpr;
use sexpr::*;

mod build;
use build::*;

#[derive(Debug)]
pub struct NonterminalDef {
    ty: Ty,
    rules: Vec<ProdRule>,
}

#[derive(Debug)]
pub struct SynthFun {
    args: IndexMap<String, Ty>,
    ret: Ty,
    nonterminals: IndexMap<String, Ty>,
    nonterminal_defs: IndexMap<String, NonterminalDef>,
}

#[derive(Debug)]
pub enum ProdRule {
    NonTerminal(String),
    Const(String),
    Op(String, Vec<ProdRule>),
}

#[derive(Debug)]
// TODO support let.
pub struct Expr {
    op: String,
    children: Vec<Expr>,
}

#[derive(Debug)]
enum Logic {
    LIA,
    BitVec,
}

#[derive(Debug)]
struct DefinedFun {
    ret: Ty,
    args: IndexMap<String, Ty>,
    expr: Expr,
}

#[derive(Debug, Default)]
pub struct SynthProblem {
    logic: Option<Logic>,
    synthfuns: IndexMap<String, SynthFun>,
    constraints: Vec<Expr>,
    defined_funs: IndexMap<String, DefinedFun>,
    declared_vars: IndexMap<String, Ty>,
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

