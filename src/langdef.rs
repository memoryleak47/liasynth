use crate::*;
use lang::define_language;

define_language! {
    [
        (Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}),
		(Maxf0, [Ty::Int, Ty::Int], Ty::Int, "max-f", "(max-f ? ?)", Value::Int(if (to_int(ev(0)?) > to_int(ev(1)?)) { to_int(ev(0)?) } else { to_int(ev(1)?) } )),
		(Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ?)", { let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}),
		(Or, [Ty::Bool, Ty::Bool], Ty::Bool, "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
		(Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
		(Sub, [Ty::Int, Ty::Int], Ty::Int, "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?))),
		(Add, [Ty::Int, Ty::Int], Ty::Int, "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
		(Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))),
		(Gte, [Ty::Int, Ty::Int], Ty::Bool, ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))),
		(Not, [Ty::Bool], Ty::Bool, "not", "(not ?)", Value::Bool(!to_bool(ev(0)?))),
		(Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))),
		(Ite, [Ty::Bool, Ty::Int, Ty::Int], Ty::Int, "ite", "(ite ? ? ?)", (if to_bool(ev(0)?) { ev(1)? } else { ev(2)? })),
		(Equals, [Ty::Int, Ty::Int], Ty::Bool, "=", "(= ? ?)", Value::Bool(ev(0)? == ev(1)?)),
		(Mul, [Ty::Int, Ty::Int], Ty::Int, "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
		(Add0, [Ty::Int, Ty::Int], Ty::Int, "+", "(+ x x)", Value::Int(to_int(ev(0)?) + to_int(ev(0)?))),
		(Lte, [Ty::Int, Ty::Int], Ty::Bool, "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
		(Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),
		(Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),
		(And, [Ty::Bool, Ty::Bool], Ty::Bool, "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
		(Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
		(Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?))
    ]
}
        