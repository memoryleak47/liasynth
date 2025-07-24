use std::fmt::{Debug, Display, Formatter, Result};
use std::str::FromStr;

use crate::*;

impl Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Bool(b) => write!(f, "{b}"),
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "v{}", self.0)
    }
}

impl FromStr for Var {
    type Err = ();

    fn from_str(s: &str) -> std::result::Result<Self, ()> {
        if !s.starts_with("v") { return Err(()); }
        let Ok(u) = usize::from_str(&s[1..]) else { return Err(()) };
        Ok(Var(u))
    }
}
