use crate::*;
use lang::define_language;

define_language! {
    [
        // https://smt-lib.org/theories-Core.shtml
        (Not, [Ty::Bool], Ty::Bool, "not", Value::Bool(!to_bool(ev(0)))),
        (Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", Value::Bool(!to_bool(ev(0)) || to_bool(ev(1)))),
        (And, [Ty::Bool, Ty::Bool], Ty::Bool, "and", Value::Bool(to_bool(ev(0)) && to_bool(ev(1)))),
        (Or, [Ty::Bool, Ty::Bool], Ty::Bool, "or", Value::Bool(to_bool(ev(0)) || to_bool(ev(1)))),
        (Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", Value::Bool(to_bool(ev(0)) != to_bool(ev(1)))),
        (Equals, [Ty::Int, Ty::Int], Ty::Bool, "=", Value::Bool(to_int(ev(0)) == to_int(ev(1)))),
        (Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", Value::Bool(to_int(ev(0)) != to_int(ev(1)))),
        (Ite, [Ty::Bool, Ty::Int, Ty::Int], Ty::Int, "ite", (if to_bool(ev(0)) { ev(1) } else { ev(2) })),

        // https://smt-lib.org/theories-Ints.shtml
        (Neg, [Ty::Int], Ty::Int, "-", Value::Int(-to_int(ev(0)))),
        (Sub, [Ty::Int, Ty::Int], Ty::Int, "-", Value::Int(to_int(ev(0)) - to_int(ev(1)))),
        (Add, [Ty::Int, Ty::Int], Ty::Int, "+", Value::Int(to_int(ev(0)) + to_int(ev(1)))),
        (Mul, [Ty::Int, Ty::Int], Ty::Int, "*", Value::Int(to_int(ev(0)) / to_int(ev(1)))),
        (Div, [Ty::Int, Ty::Int], Ty::Int, "/", Value::Int(to_int(ev(0)) / to_int(ev(1)))),
        (Mod, [Ty::Int, Ty::Int], Ty::Int, "%", Value::Int(to_int(ev(0)) % to_int(ev(1)))),
        (Abs, [Ty::Int], Ty::Int, "abs", Value::Int(to_int(ev(0)).abs())),

        (Lte, [Ty::Int, Ty::Int], Ty::Bool, "<=", Value::Bool(to_int(ev(0)) <= to_int(ev(1)))),
        (Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", Value::Bool(to_int(ev(0)) < to_int(ev(1)))),
        (Gte, [Ty::Int, Ty::Int], Ty::Bool, ">=", Value::Bool(to_int(ev(0)) >= to_int(ev(1)))),
        (Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", Value::Bool(to_int(ev(0)) > to_int(ev(1)))),
    ]
}
