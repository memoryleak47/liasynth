use std::fmt::{Debug, Display, Formatter, Result};

use crate::*;

pub fn term_to_z3(t: &Term, vars: &[String]) -> String {
    term_to_z3_impl(t.elems.len() - 1, t, vars)
}

fn term_to_z3_impl(i: usize, t: &Term, vars: &[String]) -> String {
    match &t.elems[i] {
        Node::Var(v) => vars.get(*v).cloned().unwrap_or_else(|| format!("v{v}")),

        &Node::Add([x, y]) => format!("(+ {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Sub([x, y]) => format!("(- {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Mul([x, y]) => format!("(* {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Div([x, y]) => format!("(div {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Mod([x, y]) => format!("(mod {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),

        &Node::Ite([x, y, z]) => format!("(ite {} {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars), term_to_z3_impl(z, t, vars)),
        &Node::Lt([x, y]) => format!("(< {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Gt([x, y]) => format!("(> {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Lte([x, y]) => format!("(<= {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Gte([x, y]) => format!("(>= {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Equals([x, y]) => format!("(= {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Abs([x]) => format!("(abs {})", term_to_z3_impl(x, t, vars)),
        &Node::Not([x]) => format!("(not {})", term_to_z3_impl(x, t, vars)),
        &Node::Neg([x]) => format!("(-{})", term_to_z3_impl(x, t, vars)),
        &Node::True => format!("true"),
        &Node::False => format!("false"),
        &Node::And([x, y]) => format!("(and {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Or([x, y]) => format!("(or {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Implies([x, y]) => format!("(=> {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Xor([x, y]) => format!("(xor {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),
        &Node::Distinct([x, y]) => format!("(distinct {} {})", term_to_z3_impl(x, t, vars), term_to_z3_impl(y, t, vars)),

        Node::ConstInt(i) => format!("{i}"),
    }
}


