use indexmap::IndexMap;
use std::fmt::*;
use crate::Ty;

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

#[derive(Debug)]
pub struct SynthProblem {
    logic: Logic,
    synthfuns: Vec<SynthFun>,
    constraints: Vec<Expr>,
    defined_funs: Vec<DefinedFun>,
    declared_vars: Vec<DeclaredVar>,
}

#[derive(PartialEq, Eq)]
enum SExpr {
    Ident(String),
    List(Vec<SExpr>),
}

impl Debug for SExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        print(self, f, 0)
    }
}

fn print(expr: &SExpr, f: &mut Formatter<'_>, indent: usize) -> Result {
    match expr {
        SExpr::Ident(id) => write!(f, "{id}", ),
        SExpr::List(l) => {
            write!(f, "(")?;
            for (i, x) in l.iter().enumerate() {
                print(x, f, indent+2);
                if i != l.len()-1 {
                    write!(f, " ")?;
                }
            }
            write!(f, ")\n")?;
            for _ in 0..indent {
                write!(f, " ")?;
            }
            Ok(())
        },
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token {
    Ident(String),
    LParen,
    RParen,
}

fn tokenize(s: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut svec = Vec::new();

    svec.push('(');
    svec.extend(s.chars());
    svec.push(')');

    let mut s: &[char] = &svec[..];

    while s.len() > 0 {
        match s[0] {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            x if x.is_whitespace() => {},
            x => {
                let i = s.iter().position(|x| x.is_whitespace() || *x == '(' || *x == ')').unwrap();
                tokens.push(Token::Ident(s[0..i].iter().collect()));
                s = &s[i..];
                continue;
            },
        }
        s = &s[1..];
    }

    tokens
}

fn assemble(toks: &[Token]) -> Option<(SExpr, &[Token])> {
    match toks {
        [Token::LParen, toks@..] => {
            let mut toks = toks;
            let mut subexprs = Vec::new();
            while let Some((expr, toks2)) = assemble(toks) {
                toks = toks2;
                subexprs.push(expr);
            }
            if toks[0] != Token::RParen { return None; }
            let toks = &toks[1..];

            Some((SExpr::List(subexprs), toks))
        },
        [Token::Ident(id), toks@..] => Some((SExpr::Ident(id.clone()), toks)),
        [Token::RParen, ..] => None,
        [] => None,
    }
}

fn build_synth(expr: &SExpr) -> SynthProblem {
    todo!()
}

pub fn parse_synth(s: &str) -> SynthProblem {
    let toks = tokenize(s);
    let (expr, toks) = assemble(&toks).unwrap();
    assert!(toks.is_empty());
    build_synth(&expr)
}
