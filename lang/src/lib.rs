use proc_macro::TokenStream as TokenStream1;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::*;

const DEBUG: bool = false;

struct Case {
    ident: Expr,
    retty: Expr,
    argtys: Vec<Expr>,
    symb: Expr,
    compute: Expr,
}

struct EnumDef {
    cases: Vec<Case>,
}

fn build_enum_def(input: TokenStream1) -> EnumDef {
    let mut arr: ExprArray = parse(input).unwrap();

    let mut cases: Vec<Case> = Vec::new();
    for x in arr.elems.iter() {
        let Expr::Tuple(tup) = x else { panic!() };
        let [ident, argtys, retty, symb, compute] = &*tup.elems.iter().collect::<Box<[_]>>() else { panic!() };
        let Expr::Array(argtys) = argtys else { panic!() };
        let n = LitInt::new(&argtys.elems.len().to_string(), proc_macro2::Span::call_site());
        let case = Case {
            ident: (**ident).clone(),
            argtys: argtys.elems.iter().cloned().collect(),
            retty: (*retty).clone(),
            symb: (*symb).clone(),
            compute: (*compute).clone(),
        };
        cases.push(case);
    }

    EnumDef {
        cases,
    }
}

#[proc_macro]
pub fn define_language(input: TokenStream1) -> TokenStream1 {
    let edef: EnumDef = build_enum_def(input);

    let enum_cases = enum_cases(&edef);
    let signature_cases = signature_cases(&edef);
    let get_children_cases = get_children_cases(&edef);
    let get_children_mut_cases = get_children_mut_cases(&edef);
    let eval_cases = eval_cases(&edef);
    let extract_cases = extract_cases(&edef);
    let parse_cases = parse_cases(&edef);

    let out: TokenStream1 = quote! {
        #[derive(PartialEq, Eq, Hash, Clone, Debug, PartialOrd, Ord)]
        pub enum Node {
            ConstInt(Int),
            True,
            False,
            VarInt(Var),
            VarBool(Var),
            #(#enum_cases),*
        }

        impl Node {
            pub fn signature(&self) -> &'static (&'static [Ty], Ty) {
                match self {
                    Node::ConstInt(i) => &(&[], Ty::Int),
                    Node::True => &(&[], Ty::Bool),
                    Node::False => &(&[], Ty::Bool),
                    Node::VarInt(v) => &(&[], Ty::Int),
                    Node::VarBool(v) => &(&[], Ty::Bool),
                    #(#signature_cases),*
                }
            }

            pub fn children(&self) -> &[Id] {
                match self {
                    Node::ConstInt(_) | Node::True | Node::False | Node::VarInt(_) | Node::VarBool(_) => &[],
                    #(#get_children_cases),*
                }
            }

            pub fn children_mut(&mut self) -> &mut [Id] {
                match self {
                    Node::ConstInt(_) | Node::True | Node::False | Node::VarInt(_) | Node::VarBool(_) => &mut [],
                    #(#get_children_mut_cases),*
                }
            }

            pub fn eval(&self, ch: impl Fn(Id) -> Value, sigma: &Sigma) -> Value {
                match self {
                    Node::ConstInt(i) => Value::Int(*i),
                    Node::True => Value::Bool(true),
                    Node::False => Value::Bool(false),
                    Node::VarInt(v) | Node::VarBool(v) => sigma.get(*v).unwrap_or_else(|| panic!("Failed {sigma:?} index with {v}")).clone(),
                    #(#eval_cases),*
                }
            }

            pub fn extract(&self, ex: &impl Fn(Id) -> Node, out: &mut Vec<Node>) {
                match self {
                    a@(Node::ConstInt(_) | Node::True | Node::False | Node::VarInt(_) | Node::VarBool(_)) => out.push(a.clone()),
                    #(#extract_cases),*
                }
            }

            pub fn parse(op: &str, args: &[Id]) -> Option<Node> {
                match (op, args) {
                    #(#parse_cases,)*
                    _ => None,
                }
            }
        }
    }
    .to_token_stream()
    .into();

    if DEBUG {
        println!("----------");
        println!("{}", out.to_string());
        println!("----------");
    }

    out
}

fn enum_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let n = c.argtys.len();
        let v = quote! {
            #ident([Id; #n])
        };
        cases.push(v);
    }
    cases
}

fn signature_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let retty = &c.retty;
        let argtys = &c.argtys;
        let args = quote! {
            &[#(#argtys),*]
        };

        let v = quote! {
            Node::#ident(_) => &(#args, #retty)
        };
        cases.push(v);
    }
    cases
}

fn get_children_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let v = quote! {
            Node::#ident(s) => s
        };
        cases.push(v);
    }
    cases
}

fn get_children_mut_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let v = quote! {
            Node::#ident(s) => s
        };
        cases.push(v);
    }
    cases
}

fn eval_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let compute = &c.compute;
        let v = quote! {
            Node::#ident(s) => {
                let ev = |x: usize| -> Value { ch(s[x]) };
                #compute
            }
        };
        cases.push(v);
    }
    cases
}

fn extract_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let compute = &c.compute;
        let v = quote! {
            Node::#ident(s) => {
                let mut a = self.clone();
                for child in a.children_mut() {
                    let child: &mut Id = child;
                    ex(*child).extract(ex, out);
                    *child = out.len() - 1;
                }
                out.push(a);
            }
        };
        cases.push(v);
    }
    cases
}

fn parse_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases: Vec<TokenStream2> = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let symb = &c.symb;
        let n = c.argtys.len();
        let v = quote! {
            (#symb, s) if s.len() == #n => Some(Node::#ident(s.iter().cloned().collect::<Vec<_>>().try_into().unwrap()))
        };
        cases.push(v);
    }
    cases
}
