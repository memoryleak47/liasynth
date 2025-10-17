use crate::*;
use lang::define_language;

define_language! {
    [
        (Or, [Ty::PRule(2), Ty::PRule(2)], Ty::NonTerminal(0), "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
	(Mul, [Ty::PRule(16), Ty::PRule(32)], Ty::NonTerminal(3), "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
	(Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
	(Ite, [Ty::Bool, Ty::Int, Ty::Int], Ty::Int, "ite", "(ite ? ? ?)", Value::Int(if to_bool(ev(0)?) { to_int(ev(1)?) } else { to_int(ev(2)?) })),
	(Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))),
	(Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
	(Not, [Ty::Bool], Ty::Bool, "not", "(not ?)", Value::Bool(!to_bool(ev(0)?))),
	(Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))),
	(Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ? ?)", { let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}),
	(And, [Ty::PRule(2), Ty::PRule(2)], Ty::NonTerminal(0), "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
	(Add1, [Ty::PRule(64), Ty::PRule(64)], Ty::NonTerminal(6), "+1", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
	(Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),
	(Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?)),
	(Sub, [Ty::PRule(64), Ty::PRule(64)], Ty::NonTerminal(6), "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?))),
	(Lte, [Ty::PRule(4), Ty::PRule(64)], Ty::NonTerminal(1), "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
	(Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}),
	(Add, [Ty::PRule(8), Ty::PRule(8)], Ty::NonTerminal(2), "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
	(Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),
	(Equals, [Ty::PRule(4), Ty::PRule(64)], Ty::NonTerminal(1), "=", "(= ? ?)", Value::Bool(to_int(ev(0)?) == to_int(ev(1)?))),
	(Gte, [Ty::Int, Ty::Int], Ty::Bool, ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?)))
    ]
}
        