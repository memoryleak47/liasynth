use std::fmt::{Debug, Display, Formatter, Result};

use crate::*;

pub fn term_to_z3(t: &Term, vars: &[String]) -> String {
    term_to_z3_impl(t.elems.len() - 1, t, vars)
}

fn child_to_z3(c: &Child, t: &Term, vars: &[String]) -> String {
    match *c {
        Child::Hole(id)     => term_to_z3_impl(id, t, vars),
        Child::Constant(c)  => format!("{c}"),
        Child::VarInt(v)    => vars.get(v).cloned().unwrap_or_else(|| format!("v{v}")),
        Child::VarBool(v)   => vars.get(v).cloned().unwrap_or_else(|| format!("b{v}")),
    }
}

fn term_to_z3_impl(i: usize, t: &Term, vars: &[String]) -> String {
    match &t.elems[i] {
        Node::PlaceHolder(i)                => format!("{i}"),
        Node::VarInt(v) | Node::VarBool(v)  => vars.get(*v).cloned().unwrap_or_else(|| format!("v{v}")),

        Node::Add(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(+ {} {})",      c(0), c(1)) }
        Node::Sub(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(- {} {})",      c(0), c(1)) }
        Node::Mul(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(* {} {})",      c(0), c(1)) }
        Node::Div(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(div {} {})",    c(0), c(1)) }
        Node::Mod(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(mod {} {})",    c(0), c(1)) }

        Node::Ite(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(ite {} {} {})", c(0), c(1), c(2)) }
        Node::Lt(s)       => { let c = |k| child_to_z3(&s[k], t, vars); format!("(< {} {})",      c(0), c(1)) }
        Node::Gt(s)       => { let c = |k| child_to_z3(&s[k], t, vars); format!("(> {} {})",      c(0), c(1)) }
        Node::Lte(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(<= {} {})",     c(0), c(1)) }
        Node::Gte(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(>= {} {})",     c(0), c(1)) }
        Node::Equals(s)   => { let c = |k| child_to_z3(&s[k], t, vars); format!("(= {} {})",      c(0), c(1)) }
        Node::Abs(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(abs {})",       c(0)) }
        Node::Not(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(not {})",       c(0)) }
        Node::Neg(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(- {})",         c(0)) }
        Node::True        => "true".to_string(),
        Node::False       => "false".to_string(),
        Node::And(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(and {} {})",    c(0), c(1)) }
        Node::Or(s)       => { let c = |k| child_to_z3(&s[k], t, vars); format!("(or {} {})",     c(0), c(1)) }
        Node::Implies(s)  => { let c = |k| child_to_z3(&s[k], t, vars); format!("(=> {} {})",     c(0), c(1)) }
        Node::Xor(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(xor {} {})",    c(0), c(1)) }
        Node::Distinct(s) => { let c = |k| child_to_z3(&s[k], t, vars); format!("(distinct {} {})", c(0), c(1)) }

        Node::ConstInt(i) => format!("{i}"),

        // Adjust any custom nodes similarly:
        Node::Tmp(s)      => { let c = |k| child_to_z3(&s[k], t, vars); format!("(ite (> {} {}) {} {})", c(0), c(1), c(2), c(3)) }
        Node::Tmp2(s)     => { let c = |k| child_to_z3(&s[k], t, vars); format!("(+ (+ 10 {}) {})",      c(0), c(1)) }
    }
}
