use std::fmt::{Debug, Display, Formatter, Result};

use crate::*;

pub fn term_to_z3(t: &Term, vars: &[String]) -> String {
    term_to_z3_impl(t.elems.len() - 1, t, vars)
}

fn term_to_z3_impl(i: usize, t: &Term, vars: &[String]) -> String {
    let n = &t.elems[i];
    match n {
        Node::PlaceHolder(id)               => id.to_string(),
        Node::ConstInt(k)                   => k.to_string(),
        Node::VarInt(v) | Node::VarBool(v)  => vars.get(*v).cloned().unwrap_or_else(|| format!("v{v}")),
        _ => {
            let tmpl = n.template().expect("node missing template");
            let args = n.children()
                .iter()
                .filter(|c| matches!(c, Child::Hole(_)))
                .map(|c| {
                        child_to_z3(c, t, vars)
                })
                .collect::<Vec<_>>();
            fill_template(tmpl, &args)
        }
    }
}

fn child_to_z3(c: &Child, t: &Term, vars: &[String]) -> String {
    match *c {
        Child::Hole(id)    => term_to_z3_impl(id, t, vars),
        Child::Constant(c) => c.to_string(),
        Child::VarInt(v)   => vars.get(v).cloned().unwrap_or_else(|| format!("v{v}")),
        Child::VarBool(v)  => vars.get(v).cloned().unwrap_or_else(|| format!("b{v}")),
    }
}

fn fill_template(template: &str, args: &[String]) -> String {
    let mut it = args.iter();
    let mut out = String::with_capacity(template.len() + args.iter().map(|s| s.len()).sum::<usize>());
    for ch in template.chars() {
        if ch == '?' {
            out.push_str(it.next().expect("arity/template mismatch"));
        } else {
            out.push(ch);
        }
    }
    debug_assert!(it.next().is_none(), "too many args for template");
    out
}
