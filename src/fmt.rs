use std::fmt::{Debug, Formatter, Result};

use crate::*;

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", rec(self.elems.len()-1, self))
    }
}

fn rec(i: usize, t: &Term) -> String {
    match &t.elems[i] {
        Node::Var(v) => format!("v{v}"),

        &Node::Add([x, y]) => format!("(add {} {})", rec(x, t), rec(y, t)),
        &Node::Sub([x, y]) => format!("(sub {} {})", rec(x, t), rec(y, t)),
        &Node::Mul([x, y]) => format!("(mul {} {})", rec(x, t), rec(y, t)),
        &Node::Div([x, y]) => format!("(div {} {})", rec(x, t), rec(y, t)),

        &Node::Ite([x, y, z]) => format!("(ite {} {} {})", rec(x, t), rec(y, t), rec(z, t)),
        &Node::Lt([x, y]) => format!("(lt {} {})", rec(x, t), rec(y, t)),

        Node::Constant(i) => format!("{i}"),
    }
}
