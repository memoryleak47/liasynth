use indexmap::IndexMap;
use std::fmt::*;
use crate::Ty;

mod sexpr;
use sexpr::*;

mod build;
use build::*;

#[derive(Debug, Clone)]
pub struct NonterminalDef {
    ty: Ty,
    rules: Vec<ProdRule>,
}

#[derive(Debug, Clone)]
pub struct SynthFun {
    args: IndexMap<String, Ty>,
    ret: Ty,
    nonterminals: IndexMap<String, Ty>,
    nonterminal_defs: IndexMap<String, NonterminalDef>,
}

#[derive(Debug, Clone)]
pub enum ProdRule {
    NonTerminal(String),
    Op(String, Vec<ProdRule>),
    Const(String), // what does Const include?
}

#[derive(Debug, Clone)]
pub enum Expr {
    Op(String, Vec<Expr>),
    Let(IndexMap<String, Expr>, Box<Expr>),
    Const(String), // what does Const include?
}

#[derive(Debug, Clone)]
enum Logic {
    LIA,
    BitVec,
}

#[derive(Debug, Clone)]
struct DefinedFun {
    ret: Ty,
    args: IndexMap<String, Ty>,
    expr: Expr,
}

#[derive(Debug, Default, Clone)]
pub struct SynthProblem {
    pub logic: Option<Logic>,
    pub synthfuns: IndexMap<String, SynthFun>,
    pub constraints: Vec<Expr>,
    pub defined_funs: IndexMap<String, DefinedFun>,
    pub declared_vars: IndexMap<String, Ty>,
    pub check_synth: bool,
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

