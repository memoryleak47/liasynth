use std::fmt::{Debug, Display, Formatter, Result};

use crate::*;

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", term_to_z3(self.elems.len()-1, self, &[], ""))
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", term_to_z3(self.elems.len()-1, self, &[], ""))
    }
}

pub fn term_to_z3(i: usize, t: &Term, vars: &[String], progname: &str) -> String {
    match &t.elems[i] {
        Node::Var(v) => vars.get(*v).cloned().unwrap_or_else(|| format!("unknown_{v}")),

        &Node::Add([x, y]) => format!("(+ {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Sub([x, y]) => format!("(- {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Mul([x, y]) => format!("(* {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Div([x, y]) => format!("(div {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Mod([x, y]) => format!("(mod {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),

        &Node::Ite([x, y, z]) => format!("(ite {} {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname), term_to_z3(z, t, vars, progname)),
        &Node::Lt([x, y]) => format!("(< {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Gt([x, y]) => format!("(> {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Lte([x, y]) => format!("(<= {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Gte([x, y]) => format!("(>= {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Equals([x, y]) => format!("(= {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Abs([x]) => format!("(abs {})", term_to_z3(x, t, vars, progname)),
        &Node::Not([x]) => format!("(not {})", term_to_z3(x, t, vars, progname)),
        &Node::Neg([x]) => format!("(-{})", term_to_z3(x, t, vars, progname)),
        &Node::True => format!("true"),
        &Node::False => format!("false"),
        &Node::And([x, y]) => format!("(and {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Or([x, y]) => format!("(or {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Implies([x, y]) => format!("(=> {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Xor([x, y]) => format!("(xor {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),
        &Node::Distinct([x, y]) => format!("(distinct {} {})", term_to_z3(x, t, vars, progname), term_to_z3(y, t, vars, progname)),

        Node::ConstInt(i) => format!("{i}"),
        Node::SynthCall(args) => {
            let mut s = String::new();
            s.push('(');
            s.push_str(progname);
            s.push(' ');
            for x in args {
                s.push_str(&term_to_z3(*x, t, vars, progname));
                s.push(' ');
            }
            s.push(')');
            s
        }
    }
}


