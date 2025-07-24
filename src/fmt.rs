use std::fmt::{Debug, Formatter, Result};
use crate::*;

impl Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Bool(b) => write!(f, "{b}"),
        }
    }
}
