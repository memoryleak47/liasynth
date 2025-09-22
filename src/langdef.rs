use crate::*;
use lang::define_language;


// TODO: Idea is to use the fourth element as a regex-like for how to parse and how to format
// means we dont need the fmt implemented for language
define_language! {
    [
        // https://smt-lib.org/theories-Core.shtml
        (Not, [Ty::Bool], Ty::Bool, "not", "(not ?)", Value::Bool(!to_bool(ev(0)?))),
        (Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))),
        (And, [Ty::Bool, Ty::Bool], Ty::Bool, "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
        (Or, [Ty::Bool, Ty::Bool], Ty::Bool, "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
        (Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
        (Equals, [Ty::Int, Ty::Int], Ty::Bool, "=", "(= ? ?)", Value::Bool(ev(0)? == ev(1)?)),
        (Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?)),
        (Ite, [Ty::Bool, Ty::Int, Ty::Int], Ty::Int, "ite", "(ite ? ? ?)", (if to_bool(ev(0)?) { ev(1)? } else { ev(2)? })),

        // https://smt-lib.org/theories-Ints.shtml
        (Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
        (Sub, [Ty::Int, Ty::Int], Ty::Int, "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?))),
        (Add, [Ty::Int, Ty::Int], Ty::Int, "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
        (Mul, [Ty::Int, Ty::Int], Ty::Int, "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
        (Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {
            let b = ev(1)?;
            if b == Value::Int(0) { return None }
            else { Value::Int(to_int(ev(0)?) / to_int(b)) }
        }),
        (Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ?)", {
            let b = ev(1)?;
            if b == Value::Int(0) { return None }
            else { Value::Int(to_int(ev(0)?) % to_int(b)) }
        }),
        (Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),

        (Lte, [Ty::Int, Ty::Int], Ty::Bool, "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
        (Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))),
        (Gte, [Ty::Int, Ty::Int], Ty::Bool, ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))),
        (Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),

        // BUG: This is wrong
        // The arguments in the condition are wrong as they should be hard coded as x and y
        // Maybe this takes 4 arguments, two bound to x and y and two as free arguments
        (Tmp, [Ty::Int, Ty::Int],  Ty::Int, "tmp", "(ite (> x y) ? ?)", Value::Int(if to_int(ev(0)?) > to_int(ev(1)?) { to_int(ev(0)?) } else { to_int(ev(1)? ) })),
    ]
}
