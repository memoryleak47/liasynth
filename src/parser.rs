use thiserror::Error;

use lazy_static::lazy_static;
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use winnow::{
    ascii::{alpha1, multispace0, multispace1, digit1},
    combinator::{alt, delimited, preceded, repeat, repeat_till, separated_pair, seq},
    error::{ContextError, Result as PResult},
    prelude::*,
    token::take_while,
};


type SubType = String;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Any,
}


#[derive(Debug, Clone, PartialEq, Eq)]
enum SymbolTableVal {
    Term(String, Type),
    NonTerm(NonTerm),
}

lazy_static! {
    static ref SYMBOL_TABLE: Mutex<HashMap<String, SymbolTableVal>> = Mutex::new(HashMap::new());
    static ref FUNCS_TABLE: Mutex<HashMap<String, SymbolTableVal>> = Mutex::new(HashMap::new());
    static ref GRAMMAR_TABLE: Mutex<HashMap<String, Type>> = Mutex::new(HashMap::new());
}

fn add_to_table(name: String, val: SymbolTableVal) {
    let mut table = SYMBOL_TABLE.lock().unwrap();
    table.insert(name, val);
}

fn lookup_in_symbol_table(name: &str) -> Option<SymbolTableVal> {
    SYMBOL_TABLE.lock().unwrap().get(name).cloned()
}

#[allow(dead_code)]
fn print_symbol_table() {
    let table = SYMBOL_TABLE.lock().unwrap();
    for (key, value) in table.iter() {
        println!("{}: {:?}", key, value);
    }
}

fn add_to_grammar_table(name: String, val: Type) {
    let mut table = GRAMMAR_TABLE.lock().unwrap();
    table.insert(name, val);
}

fn lookup_grammar_table(gram: &str) -> Option<Type> {
    GRAMMAR_TABLE.lock().unwrap().get(gram).cloned()
}

#[allow(dead_code)]
fn print_grammar_table() {
    let table = GRAMMAR_TABLE.lock().unwrap();
    for (key, value) in table.iter() {
        println!("{}: {:?}", key, value);
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Theory {
    LIA,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Num(i32),
    Bool(bool),
    Var(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Term(Term),
    Operation {
        op: String,
        expr: Vec<Expr>,
    },
    Let {
        bindings: Vec<(String, Expr)>,
        body: Box<Expr>
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonTerm {
    pub op: String,
    pub args: Vec<(String, Type)>,
    pub ret_subtype: Option<SubType>,
    pub ret_type: Type,
    pub commutative: bool,
}

#[derive(Debug)]
enum GrammarElement {
    Term(Term),
    NonTerm(String, Vec<SubType>),
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct SubGrammar {
    pub terms: Vec<Term>,
    pub nonterms: Vec<NonTerm>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SyGuSExpr {
    SetTheory(Theory),
    Args(String, Type),
    Subtype(String, Type),
    DeclaredVar(String, Type),
    DefinedFun(String, Vec<(String, Type)>, Type, Expr),
    SynthFun(
        String,
        Vec<(String, Type)>,
        Type,
        Vec<SyGuSExpr>,
        Vec<SubGrammar>,
    ),
    Constraint(Expr),
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Parser Errors
////////////////////////////////////////////////////////////////////////////////////////////////////

#[allow(dead_code)]
#[derive(Debug, thiserror::Error)]
pub enum ParserError {
    #[error("No check-synth provided")]
    SynthError(String),
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////////////////////////

// TODO: Parse let expressions!

pub fn parse_sygus(src: &str) -> Result<(Vec<SyGuSExpr>, &str), ParserError> {

    initialize_boolean_operators();
    initialize_comparison_operators();
    initialize_maths_operators();

    repeat_till(
        1..,
        s_exp(alt((
            parse_logic,
            parse_synth_fun,
            parse_define_fun,
            parse_declare_var,
            parse_constraint,
        ))),
        ws(s_exp(ws("check-synth"))),
    )
    .parse(src)
    .map_err(|e| ParserError::SynthError(e.to_string()))
}

fn parse_logic(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    preceded(ws("set-logic"), alpha1)
    .map(|l| match l {
           "LIA" => SyGuSExpr::SetTheory(Theory::LIA),
            _ => panic!("Unknown Theory"),
    })
    .parse_next(i)
}

fn parse_synth_fun(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    preceded(
        ws("synth-fun"),
        seq! {
            ws(parse_name),
            ws(s_exp(repeat(0.., s_exp(parse_args))))
                .map(|args: Vec<_>| {
                    for arg in args.clone() {
                    if let (n, t) = arg {
                        add_to_grammar_table(n.clone(), t.clone());
                    }};

                 args
                }),
            ws(parse_type),
            ws(s_exp(repeat(0.., s_exp(parse_subtype)))),
            ws(s_exp(repeat(0.., s_exp(parse_subgrammar))))
        },
    )
    .map(|(name, args, sort, subtypes, subgrams): (String, Vec<(String, Type)>, Type, Vec<SyGuSExpr>, Vec<SubGrammar>)|{

        add_to_table(
            name.clone(),
            SymbolTableVal::NonTerm(NonTerm {
                op: name.clone(),
                args: args.clone(),
                ret_subtype: None,
                ret_type: sort.clone(),
                commutative: false,
            })
        );

        SyGuSExpr::SynthFun(name, args, sort, subtypes, subgrams)
    })
    .parse_next(i)
}

fn parse_define_fun(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    preceded(
        ws("define-fun"),
        seq! {
            ws(parse_name),
            ws(s_exp(repeat(0.., s_exp(parse_args)))),
            ws(parse_type),
            ws(parse_expr)
        }
    )
    .map(|(name, args, sort, expr): (String, Vec<(String, Type)>, Type, Expr)| {

        add_to_table(
            name.clone(),
            SymbolTableVal::NonTerm(NonTerm {
                op: name.clone(),
                args: args.clone(),
                ret_subtype: None,
                ret_type: sort.clone(),
                commutative: false,
            })
        );

        SyGuSExpr::DefinedFun(name, args, sort, expr)
    })
    .parse_next(i)
}

fn parse_declare_var(i: &mut &'_ str) -> PResult<SyGuSExpr> {
   preceded(
       ws("declare-var"),
       parse_vars,
   )
   .parse_next(i)
}


fn parse_constraint(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    preceded("constraint", parse_expr)
    .verify(|c: &Expr| {
        match verify_expr(c) {
            Ok(_) => true,
            Err(errors) => {
                for error in errors.iter() {
                    eprintln!("Verification error: {}", error);
                }
                false
            }
        }
    })
    .map(SyGuSExpr::Constraint)
    .parse_next(i)
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Parser helpers
////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn ws<'a, O1, F>(inner: F) -> impl Parser<&'a str, O1, ContextError>
where
    F: Parser<&'a str, O1, ContextError>,
{
    delimited(multispace0, inner, multispace0)
}

pub fn s_exp<'a, O1, F>(inner: F) -> impl Parser<&'a str, O1, ContextError>
where
    F: Parser<&'a str, O1, ContextError>,
{
    delimited(
        '(',
        ws(inner),
        ws(')'),
    )
}

pub fn parse_name(i: &mut &'_ str) -> PResult<String> {
    take_while(1.., |c: char| !(c.is_whitespace() || c == '(' || c == ')'))
        .map(|s: &str| s.to_string())
        .parse_next(i)
}

fn parse_type(i: &mut &'_ str) -> PResult<Type> {
    alt((
        "Int".map(|_| Type::Int),
        "Bool".map(|_| Type::Bool),
    ))
    .parse_next(i)
}

fn parse_args(i: &mut &'_ str) -> PResult<(String, Type)> {
    separated_pair(
        parse_name,
        multispace1,
        parse_type
    )
    .parse_next(i)
}

// For now this and parse_args have the same functionality
fn parse_subtype(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    separated_pair(
        parse_name,
        multispace1,
        parse_type
    )
    .map(|(name, t)| {
        add_to_grammar_table(name.clone(), t.clone());
        SyGuSExpr::Subtype(name, t)
    })
    .parse_next(i)
}

// For now this and parse_args have the same functionality
fn parse_vars(i: &mut &'_ str) -> PResult<SyGuSExpr> {
    separated_pair(
        parse_name,
        multispace1,
        parse_type
    )
    .map(|(name, t)| {
        add_to_table(
            name.clone(),
            SymbolTableVal::Term(name.clone(), t.clone())
        );

        SyGuSExpr::DeclaredVar(name, t)
    })
    .parse_next(i)
}

fn parse_subgrammar(i: &mut &'_ str) -> PResult<SubGrammar> {
    seq! {
        parse_subtype,
        ws(s_exp(repeat(0.., ws(alt((
            parse_term.map(GrammarElement::Term),
            parse_nonterm.map(|(op, args)| GrammarElement::NonTerm(op, args))
        )))))),
    }
    .map(|(subtype_expr, elements): (SyGuSExpr, Vec<GrammarElement>)| {
        let (subtype, sort) = match subtype_expr {
            SyGuSExpr::Subtype(n, t) => (n, t),
            _ => panic!("Invalid subtype expression in subgrammar"),
        };

        // Process elements into terms and nonterms
        let mut terms = Vec::new();
        let mut nonterms = Vec::new();

        for element in elements {
            match element {
                GrammarElement::Term(term) => terms.push(term),
                GrammarElement::NonTerm(op, args) => {
                    let commutative = args.iter().eq(args.iter().rev());
                    let arg_pair = args.iter()
                        .map(|arg| {
                            let exp_type = match lookup_grammar_table(arg) {
                                Some(t) => t,
                                None => panic!("No subtype found in subtype table"),
                            };
                            (arg.to_string(), exp_type)
                        })
                        .collect();

                    let nt = NonTerm {
                        op: op.clone(),
                        args: arg_pair,
                        ret_subtype: Some(subtype.clone()),
                        ret_type: sort.clone(),
                        commutative,
                    };

                    // BUG: Does this work?
                    let _op = if op == '-'.to_string() {
                        "Â¯".to_string()
                    } else {
                        op
                    };

                    add_to_table(_op, SymbolTableVal::NonTerm(nt.clone()));
                    nonterms.push(nt);
                }
            }
        }

        SubGrammar { terms, nonterms }
    })
    .verify(|SubGrammar{ terms, nonterms}| {
        terms.iter().all(|elm| {
            if let Term::Var(n) = elm {
                lookup_grammar_table(n.as_ref()).is_some()
            } else  { true  }
        })
            &&
        nonterms.iter().all(|NonTerm{op: _, args, ret_subtype: _, ret_type: _, commutative: _}| {
            args.iter().all(|e| {
                if let (n, _) = e {
                    lookup_grammar_table(n.as_ref()).is_some()
                } else  { true  }
            })
        })
    })
    .parse_next(i)
}

fn parse_term(i: &mut &'_ str) -> PResult<Term> {
    alt((
        alt(("true", "false")).try_map(|bool_str: &str| bool_str.parse::<bool>().map(|n| Term::Bool(n))),
        digit1.try_map(|digit_str: &str| digit_str.parse::<i32>().map(|n| Term::Num(n))),
        s_exp(preceded(ws('-'), ws(digit1))).try_map(|digit_str: &str| digit_str.parse::<i32>().map(|n| Term::Num(-n))),
        parse_name.map(|n| Term::Var(n)),
    ))
    .parse_next(i)
}

fn parse_nonterm(i: &mut &'_ str) -> PResult<(String, Vec<SubType>)> {
    s_exp(
        seq! {
            ws(parse_operator),
            repeat(1.., ws(parse_name))
        }
    )
    .parse_next(i)
}

fn parse_operator(i: &mut &'_ str) -> PResult<String> {
    take_while(1.., |c: char| !(c.is_whitespace() || c == '(' || c == ')'))
        .map(|s: &str| s.to_string())
        .parse_next(i)
}

pub fn parse_expr(i: &mut &'_ str) -> PResult<Expr> {
    alt((
        ws(parse_term.map(Expr::Term)),
        ws(parse_let),
        ws(s_exp(
            seq! {
                ws(parse_operator),
                repeat(0.., ws(parse_expr)),
            }
            .map(|(op, exprs)| Expr::Operation { op, expr: exprs }),
        )),
    ))
    .parse_next(i)
}

fn parse_let(i: &mut &'_ str) -> PResult<Expr> {
    s_exp(
        preceded(
            ws("let"),
            seq! {
                s_exp(repeat(1.., parse_binding)),
                ws(parse_expr)
            }
        )
    )
    .map(|(bindings, body)| Expr::Let {
        bindings,
        body: Box::new(body)
    })
    .parse_next(i)
}

fn parse_binding(i: &mut &'_ str) -> PResult<(String, Expr)> {
    s_exp(
        seq! {
            ws(parse_operator),
            ws(parse_expr)
        }
    )
    .map(|(name, expr)| (name, expr))
    .parse_next(i)
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Verification
////////////////////////////////////////////////////////////////////////////////////////////////////


#[derive(Debug, Error)]
enum VerifyError {
    #[error("Unknown variable or function: {0}")]
    UnknownSymbol(String),
    #[error("Type mismatch in argument '{0}' for function '{1}'")]
    TypeMismatch(String, String),
    #[error("Syntax error: wrong number of arguments")]
    SyntaxError,
    #[error("Shading error: '{0}'")]
    LetError(String),
}


fn initialize_comparison_operators() {
    let mut table = FUNCS_TABLE.lock().unwrap();

    // Add < and > operators
    for op in ["<", ">", ">="]  {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Int),
                    ("y".to_string(), Type::Int),
                ],
                ret_subtype: None,
                ret_type: Type::Bool,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }

    for op in ["="]  {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Any),
                    ("y".to_string(), Type::Any),
                ],
                ret_subtype: None,
                ret_type: Type::Bool,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }
}

fn initialize_maths_operators() {
    let mut table = FUNCS_TABLE.lock().unwrap();

    // Add < and > operators
    for op in ["-", "+", "div", "*"] {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Int),
                    ("y".to_string(), Type::Int),
                ],
                ret_subtype: None,
                ret_type: Type::Int,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }

    for op in ["<=", ">="] {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Int),
                    ("y".to_string(), Type::Int),
                ],
                ret_subtype: None,
                ret_type: Type::Bool,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }
}

fn initialize_boolean_operators() {
    let mut table = FUNCS_TABLE.lock().unwrap();

    // Add < and > operators
    for op in ["and", "or", "=>"] {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Bool),
                    ("y".to_string(), Type::Bool),
                ],
                ret_subtype: None,
                ret_type: Type::Bool,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }

    for op in ["ite"] {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Any),
                    ("y".to_string(), Type::Any),
                    ("y".to_string(), Type::Any),
                ],
                ret_subtype: None,
                ret_type: Type::Any,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }

    for op in ["not"] {
        table.insert(op.to_string(),
            SymbolTableVal::NonTerm(NonTerm {
                op: op.to_string(),
                args: vec![
                    ("x".to_string(), Type::Bool),
                ],
                ret_subtype: None,
                ret_type: Type::Bool,
                commutative: false,  // Note: these are not commutative!
            })
        );
    }
}

fn verify_expr(e: &Expr) -> Result<Type, Vec<VerifyError>> {
    match e {
        Expr::Term(term) => verify_term(term),
        Expr::Operation { op, expr } => verify_operation(op, expr),
        Expr::Let { bindings, body } => verify_let(bindings, body),
    }
}

fn verify_term(term: &Term) -> Result<Type, Vec<VerifyError>> {
    match term {
        Term::Num(_) => Ok(Type::Int),
        Term::Bool(_) => Ok(Type::Bool),
        Term::Var(name) => lookup_symbol_type(name),
    }
}

fn verify_operation(op: &str, expr: &[Expr]) -> Result<Type, Vec<VerifyError>> {
    let result = {
        let table1 = FUNCS_TABLE.lock().unwrap();
        if let Some(val) = table1.get(op) {
            Some(val.clone())
        } else {
            let table2 = SYMBOL_TABLE.lock().unwrap();
            table2.get(op).cloned()
        }
    };

    match result {
        Some(SymbolTableVal::NonTerm(func)) => verify_function_call(op, expr, &func),
        Some(SymbolTableVal::Term(_, _)) => Err(vec![VerifyError::UnknownSymbol(op.to_string())]),
        None => Err(vec![VerifyError::UnknownSymbol(op.to_string())]),
    }
}

fn verify_let(bindings: &[(String, Expr)], body: &Expr) -> Result<Type, Vec<VerifyError>> {
    let mut errors = Vec::new();
    let mut symbol_types = Vec::new();

    let mut seen_bindings = HashSet::new();
    for (var_name, _) in bindings {
        if !seen_bindings.insert(var_name) {
            errors.push(VerifyError::LetError(
                format!("Variable '{}' is bound multiple times in the same let expression", var_name)
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    for (var_name, expr) in bindings {
        match verify_expr(expr) {
            Ok(expr_type) => {

                symbol_types.push((var_name.clone(), expr_type));
            }
            Err(expr_errors) => {
                errors.extend(expr_errors);
            }
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    let result = {
        let mut table = SYMBOL_TABLE.lock().unwrap();

        let old_values: Vec<_> = symbol_types
            .iter()
            .filter_map(|(name, _)| {
                table
                    .remove(name)
                    .map(|old_val| (name.clone(), old_val))
            })
            .collect();

        for (name, type_) in symbol_types.iter() {
            table.insert(
                name.clone(),
                SymbolTableVal::Term(String::new(), type_.clone()),
            );
        }

        drop(table);

        let body_result = match body {
            Expr::Let { bindings: b, body: bod } => verify_let(b, bod),
            _ => verify_expr(body),
        };

        let mut table = SYMBOL_TABLE.lock().unwrap();

        for (name, old_val) in old_values {
            table.insert(name, old_val);
        }

        for (name, _) in symbol_types.iter() {
            table.remove(name);
        }

        body_result
    };

    result
}

fn verify_function_call(
    op: &str,
    expr: &[Expr],
    func: &NonTerm
) -> Result<Type, Vec<VerifyError>> {
    let func_arg_types: Vec<Type> = func.args.iter()
        .filter_map(|arg| match arg {
            (_, t) | (_, t) => Some(t.clone()),
            _ => None
        })
        .collect();

    if expr.len() != func_arg_types.len() {
        println!("expr: {:?} has len: {} which is wrong for func {}", expr, expr.len(), func.op);
        return Err(vec![VerifyError::SyntaxError]);
    }

    // Verify each argument's type
    let mut errors = Vec::new();
    for (idx, (arg, expected_type)) in expr.iter().zip(func_arg_types.iter()).enumerate() {
        match verify_expr(arg) {
            Ok(arg_type) if arg_type == *expected_type || *expected_type == Type::Any || arg_type == Type::Any => continue,
            Ok(arg_type) => {
                errors.push(VerifyError::TypeMismatch(
                format!("Argument {} type mismatch: expected {:?}, got {:?}",
                        idx+1, expected_type, arg_type),
                op.to_string(),
            ))},
            Err(arg_errors) => errors.extend(arg_errors),
        }
    }

    if errors.is_empty() {
        Ok(func.ret_type.clone())
    } else {
        Err(errors)
    }
}

fn lookup_symbol_type(name: &str) -> Result<Type, Vec<VerifyError>> {
    match lookup_in_symbol_table(name) {
        Some(SymbolTableVal::Term(_, var_type)) => Ok(var_type),
        Some(SymbolTableVal::NonTerm(nonterm)) => Ok(nonterm.ret_type),
        None => Err(vec![VerifyError::UnknownSymbol(name.to_string())]),
    }
}

