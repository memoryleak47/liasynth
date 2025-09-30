use crate::*;
use lang::define_language;

define_language! {
    [
        (Add, [Ty::NonTerminal(2), Ty::NonTerminal(2)], Ty::NonTerminal(2), "+", "(+ ? ?)", Value::Int(to_int(ev(0)?) + to_int(ev(1)?))),
	(Mod, [Ty::Int, Ty::Int], Ty::Int, "mod", "(mod ? ?)", { let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}),
	(Lt, [Ty::Int, Ty::Int], Ty::Bool, "<", "(< ? ?)", Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))),
	(Gety, [Ty::Int], Ty::NonTerminal(2), "get-y", "(get-y currPoint)", Value::Int(if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } )),
	(Gety2, [Ty::Int], Ty::NonTerminal(2), "get-y2", "(get-y o1)", Value::Int(if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } )),
	(Or, [Ty::NonTerminal(3), Ty::NonTerminal(3)], Ty::NonTerminal(3), "or", "(or ? ?)", Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))),
	(Gety1, [Ty::Int], Ty::NonTerminal(2), "get-y1", "(get-y o0)", Value::Int(if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } )),
	(Div, [Ty::Int, Ty::Int], Ty::Int, "div", "(div ? ?)", {let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}),
	(Lte, [Ty::NonTerminal(2), Ty::NonTerminal(2)], Ty::NonTerminal(3), "<=", "(<= ? ?)", Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))),
	(Getx1, [Ty::Int], Ty::NonTerminal(2), "get-x1", "(get-x o0)", Value::Int(to_int(ev(0)?) - ((if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } ) * 10))),
	(And, [Ty::NonTerminal(3), Ty::NonTerminal(3)], Ty::NonTerminal(3), "and", "(and ? ?)", Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))),
	(Ite, [Ty::NonTerminal(3), Ty::NonTerminal(0), Ty::NonTerminal(0)], Ty::NonTerminal(0), "ite", "(ite ? ? ?)", Value::Int(if to_bool(ev(0)?) { to_int(ev(1)?) } else { to_int(ev(2)?) } )),
	(Xor, [Ty::Bool, Ty::Bool], Ty::Bool, "xor", "(xor ? ?)", Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))),
	(Equals, [Ty::NonTerminal(2), Ty::NonTerminal(2)], Ty::NonTerminal(3), "=", "(= ? ?)", Value::Bool(to_int(ev(0)?) == to_int(ev(1)?))),
	(Neg, [Ty::Int], Ty::Int, "-", "(- ?)", Value::Int(-to_int(ev(0)?))),
	(Not, [Ty::NonTerminal(3)], Ty::NonTerminal(3), "not", "(not ?)", Value::Bool(! to_bool(ev(0)?))),
	(Getx2, [Ty::Int], Ty::NonTerminal(2), "get-x2", "(get-x o1)", Value::Int(to_int(ev(0)?) - ((if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } ) * 10))),
	(Gte, [Ty::NonTerminal(2), Ty::NonTerminal(2)], Ty::NonTerminal(3), ">=", "(>= ? ?)", Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))),
	(Mul, [Ty::Int, Ty::Int], Ty::Int, "*", "(* ? ?)", Value::Int(to_int(ev(0)?) * to_int(ev(1)?))),
	(Gt, [Ty::Int, Ty::Int], Ty::Bool, ">", "(> ? ?)", Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))),
	(Getx, [Ty::Int], Ty::NonTerminal(2), "get-x", "(get-x currPoint)", Value::Int(to_int(ev(0)?) - ((if (to_int(ev(0)?) < 10) { 0 } else { (if (to_int(ev(0)?) < 20) { 1 } else { (if (to_int(ev(0)?) < 30) { 2 } else { (if (to_int(ev(0)?) < 40) { 3 } else { (if (to_int(ev(0)?) < 50) { 4 } else { (if (to_int(ev(0)?) < 60) { 5 } else { (if (to_int(ev(0)?) < 70) { 6 } else { (if (to_int(ev(0)?) < 80) { 7 } else { (if (to_int(ev(0)?) < 90) { 8 } else { 9 } ) } ) } ) } ) } ) } ) } ) } ) } ) * 10))),
	(Abs, [Ty::Int], Ty::Int, "abs", "(abs ?)", Value::Int(to_int(ev(0)?).abs())),
	(Implies, [Ty::Bool, Ty::Bool], Ty::Bool, "=>", "(=> ? ?)", Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))),
	(Distinct, [Ty::Int, Ty::Int], Ty::Bool, "distinct", "(distinct ? ?)", Value::Bool(ev(0)? != ev(1)?)),
	(Sub, [Ty::NonTerminal(2), Ty::NonTerminal(2)], Ty::NonTerminal(2), "-", "(- ? ?)", Value::Int(to_int(ev(0)?) - to_int(ev(1)?)))
    ]
}
        