use crate::*;
use lang::define_language;

define_language! {
    [
        (Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),
		(Gte, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(1), ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))),
		(Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?)),
		(Ite, [Ty::NonTerminal(1), Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "ite", "(ite ? ? ?)", Value::Int(if to_bool(ev(0)?) { to_int(ev(1)?) } else { to_int(ev(2)?) } )),
		(Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}),
		(Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))),
		(Add, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
		(And, [Ty::NonTerminal(1), Ty::NonTerminal(1)], Ty::NonTerminal(1), "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
		(Lte, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(1), "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
		(Not, [Ty::NonTerminal(1)], Ty::NonTerminal(1), "not", "(not ?)", Value::Bool(! to_bool(ev(0)?))),
		(Equals, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(1), "=", "(= ? ?)", Value::Bool(to_int(ev(0)?) == to_int(ev(1)?))),
		(Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),
		(Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
		(Mul, [Ty::Int, Ty::Int], Ty::Int, "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
		(Or, [Ty::NonTerminal(1), Ty::NonTerminal(1)], Ty::NonTerminal(1), "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
		(Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
		(Sub, [Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?))),
		(Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ? ?)", { let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}),
		(Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?)))
    ]
}
        