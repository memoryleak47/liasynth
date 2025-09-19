use indexmap::IndexMap;
use crate::*;

mod sexpr;
use sexpr::*;

mod build;
use build::*;

mod fmt;

#[derive(Debug, Clone)]
pub struct NonterminalDef {
    pub ty: Ty,
    pub prod_rules: Vec<GrammarTerm>,
}

#[derive(Debug, Clone)]
pub struct SynthFun {
    pub args: IndexMap<String, Ty>,
    pub ret: Ty,
    pub nonterminals: IndexMap<String, Ty>,
    pub nonterminal_defs: IndexMap<String, NonterminalDef>,
}

// NonTerminals defined in `nonterminals` in the SynthFun.
pub type NonTerminal = String;

// 'op' needs to be defined in
// - https://smt-lib.org/theories-Core.shtml, or
// - https://smt-lib.org/theories-Ints.shtml
// This doesn't include ops with zero arguments, like vars and constants.
pub type Op = String;

// an argument of the synth fun.
pub type SynthArg = String;

// This grammar is built from the things we've observed in the sygus benchmark.
#[derive(Debug, Clone)]
pub enum GrammarTerm {
    NonTerminal(NonTerminal),
    Op(Op, Vec<GrammarTerm>),
    ConstInt(Int), // also covers negative numbers, like this: (- 3)
    ConstBool(bool),
    SynthArg(SynthArg),
    DefinedFunCall(String, Vec<GrammarTerm>), // GrammarTerm might be NonTerminal or SynthArg.
}

#[derive(Debug, Clone)]
// used in constraints and defined funs.
pub enum Expr {
    Op(Op, Vec<Expr>),
    Let(IndexMap<String, Expr>, Box<Expr>),
    DefinedFunCall(String, Vec<Expr>),
    SynthFunCall(String, Vec<Expr>),
    Var(String), // may come from DefinedFun arg; DeclaredVar; or let.
    ConstInt(Int),
    ConstBool(bool),
}

#[derive(Debug, Clone)]
pub enum Logic {
    LIA,
    BitVec,
}

#[derive(Debug, Clone)]
pub struct DefinedFun {
    pub name: String,
    pub ret: Ty,
    pub args: IndexMap<String, Ty>,
    pub expr: Expr,
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

