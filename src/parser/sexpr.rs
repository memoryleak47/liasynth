use indexmap::IndexMap;
use std::fmt::*;
use crate::Ty;

#[derive(PartialEq, Eq, Clone)]
pub enum SExpr {
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
pub enum Token {
    Ident(String),
    LParen,
    RParen,
}

pub fn tokenize(s: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let svec: Box<[_]> = s.chars().collect();

    let mut s: &[char] = &svec[..];

    while s.len() > 0 {
        match s[0] {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            ';' => {
                let i = s.iter().position(|c| *c == '\n').unwrap();
                s = &s[i+1..];
            },
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

pub fn assemble(toks: &[Token]) -> Option<(SExpr, &[Token])> {
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
