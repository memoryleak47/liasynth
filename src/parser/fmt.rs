use crate::*;
use std::fmt::*;

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expr::ConstInt(n) => write!(f, "{n}"),
            Expr::ConstBool(b) => write!(f, "{b}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Op(op, exprs) | Expr::DefinedFunCall(op, exprs) | Expr::SynthFunCall(op, exprs) => {
                write!(f, "({op} ")?;
                for (i, c) in exprs.iter().enumerate() {
                    write!(f, "{c}")?;
                    if i != exprs.len()-1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")
            },
            Expr::Let(bindings, body) => {
                write!(f, "(let (")?;
                for (i, (var, e)) in bindings.iter().enumerate() {
                    write!(f, "({var} {e})")?;
                    if i != bindings.len()-1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ") {body})")
            },
        }
    }
}

impl Display for DefinedFun {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let DefinedFun { name, args, ret, expr } = self;
        write!(f, "(define-fun {name} (")?;
        for (i, (varname, varty)) in args.iter().enumerate() {
            let varty = varty.to_string();
            write!(f, "({varname} {varty})")?;
            if i != args.len()-1 {
                write!(f, " ")?;
            }
        }
        write!(f, ") {ret} {expr})")
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Ty::Int => write!(f, "Int"),
            Ty::Bool => write!(f, "Bool"),
            Ty::NonTerminal(i) => write!(f, "NonTerminal {}", i),
            Ty::PRule(i) => write!(f, "Rule {}", i),
        }
    }
}

