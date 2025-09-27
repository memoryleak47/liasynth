use crate::*;
use lang::define_language;

define_language! {
    [
        (Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))),
		(Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}),
		(Add, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
		(Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
		(Ite, [Ty::NonTerminal(1), Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "ite", "(ite ? ? ?)", Value::Int(if to_bool(ev(0)?) { to_int(ev(1)?) } else { to_int(ev(2)?) } )),
		(And, [Ty::Bool, Ty::Bool], Ty::Bool, "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
		(Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?)),
		(Not, [Ty::Bool], Ty::Bool, "not", "(not ?)", Value::Bool(!to_bool(ev(0)?))),
		(Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),
		(Or, [Ty::Bool, Ty::Bool], Ty::Bool, "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
		(Equals, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(1), "=", "(= ? ?)", Value::Bool(to_int(ev(0)?) == to_int(ev(1)?))),
		(Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),
		(Lte, [Ty::Int, Ty::Int], Ty::Bool, "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
		(Sub, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?))),
		(Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
		(Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ? ?)", { let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}),
		(Gte, [Ty::Int, Ty::Int], Ty::Bool, ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))),
		(Mul, [Ty::Int, Ty::Int], Ty::Int, "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
		(Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?)))
    ]
}
        