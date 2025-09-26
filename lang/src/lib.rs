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
    template: Expr,
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
        let [ident, argtys, retty, symb, template, compute] = &*tup.elems.iter().collect::<Box<[_]>>() else { panic!() };
        let Expr::Array(argtys) = argtys else { panic!() };
        let n = LitInt::new(&argtys.elems.len().to_string(), proc_macro2::Span::call_site());
        let case = Case {
            ident: (**ident).clone(),
            argtys: argtys.elems.iter().cloned().collect(),
            retty: (*retty).clone(),
            symb: (*symb).clone(),
            template: (*template).clone(),
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
    let parse_prod_cases = parse_prod_cases(&edef);
    let ident_cases = ident_cases(&edef);
    let template_cases = template_cases(&edef);

    let out: TokenStream1 = quote! {
        #[derive(PartialEq, Eq, Hash, Clone, Debug, PartialOrd, Ord)]
        pub enum Node {
            PlaceHolder(Id),
            ConstInt(Int),
            True,
            False,
            VarInt(Var),
            VarBool(Var),
            #(#enum_cases),*
        }


        #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, PartialOrd, Ord)]
        pub enum Child {
            Hole(Id),
            Constant(Int),
            VarInt(Var),
            VarBool(Var),
        }

        impl Node {
            pub fn signature(&self) -> &'static (&'static [Ty], Ty) {
                match self {
                    Node::PlaceHolder(_) => &(&[], Ty::Int),
                    Node::ConstInt(i) => &(&[], Ty::Int),
                    Node::True => &(&[], Ty::Bool),
                    Node::False => &(&[], Ty::Bool),
                    Node::VarInt(v) => &(&[], Ty::Int),
                    Node::VarBool(v) => &(&[], Ty::Bool),
                    #(#signature_cases),*
                }
            }

            pub fn template(&self) -> Option<&'static str> {
                match self {
                    Node::PlaceHolder(_)
                    | Node::ConstInt(_)
                    | Node::True
                    | Node::False
                    | Node::VarInt(_)
                    | Node::VarBool(_) => None,
                    #(#template_cases),*
                }
            }

            pub fn children(&self) -> &[Child] {
                match self {
                    Node::PlaceHolder(_)
                    | Node::ConstInt(_)
                    | Node::True
                    | Node::False
                    | Node::VarInt(_)
                    | Node::VarBool(_) => &[] as &[Child],
                    #(#get_children_cases),*
                }
            }

            pub fn children_mut(&mut self) -> &mut [Child] {
                match self {
                    Node::PlaceHolder(_)
                    | Node::ConstInt(_)
                    | Node::True
                    | Node::False
                    | Node::VarInt(_)
                    | Node::VarBool(_) => &mut [] as &mut [Child],
                    #(#get_children_mut_cases),*
                }
            }

            pub fn eval(&self, ch: impl Fn(Id) -> Option<Value>, sigma: &Sigma) -> Option<Value> {
                Some(match self {
                    Node::PlaceHolder(_) => Value::Int(0),
                    Node::ConstInt(i) => Value::Int(*i),
                    Node::True => Value::Bool(true),
                    Node::False => Value::Bool(false),
                    Node::VarInt(v) | Node::VarBool(v) => sigma.get(*v).unwrap_or_else(|| panic!("Failed {sigma:?} index with {v}")).clone(),
                    #(#eval_cases),*
                })
            }

            pub fn extract(&self, ex: &impl Fn(Id) -> Node, out: &mut Vec<Node>) {
                match self {
                    a@(Node::PlaceHolder(_) | Node::ConstInt(_) | Node::True | Node::False | Node::VarInt(_) | Node::VarBool(_)) => out.push(a.clone()),
                    #(#extract_cases),*
                }
            }

            pub fn parse(op: &str, args: &[Node]) -> Option<Node> {
                match (op, args) {
                    #(#parse_cases,)*
                    _ => None,
                }
            }

            pub fn parse_prod(op: &str, args: &[Node]) -> Option<Node> {
                match (op, args) {
                    #(#parse_prod_cases,)*
                    other => {
                        println!("parse_prod: unknown op '{:?}', args={:?}", other, args);
                        None
                    },

                }
            }

            pub fn ident(&self) -> &'static str {
                match self {
                    Node::PlaceHolder(_) => "PlaceHolder",
                    Node::ConstInt(_) => "ConstInt",
                    Node::True => "True",
                    Node::False => "False",
                    Node::VarInt(_) => "VarInt",
                    Node::VarBool(_) => "VarBool",
                    #(#ident_cases),*
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
            #ident([Child; #n])
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

fn template_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident    = &c.ident;
        let template = &c.template;
        cases.push(quote! {
            Node::#ident(_) => Some(#template)
        });
    }
    cases
}


fn get_children_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    edef.cases.iter().map(|c| {
        let ident = &c.ident;
        quote! { Node::#ident(s) => &s[..] }
    }).collect()
}

fn get_children_mut_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    edef.cases.iter().map(|c| {
        let ident = &c.ident;
        quote! { Node::#ident(s) => &mut s[..] }
    }).collect()
}

fn eval_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let compute = &c.compute;
        cases.push(quote! {
            Node::#ident(s) => {
                let ev = |x: usize| -> Option<Value> {
                    match s[x] {
                        Child::Hole(i)   => ch(i),
                        Child::Constant(c) => Some(Value::Int(c)),
                        Child::VarInt(v) => Some(sigma.get(v).cloned().unwrap_or_else(|| panic!("sigma miss {v}"))),
                        Child::VarBool(v)=> Some(sigma.get(v).cloned().unwrap_or_else(|| panic!("sigma miss {v}"))),
                    }
                };
                #compute
            }
        });
    }
    cases
}

fn extract_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        cases.push(quote! {
            Node::#ident(_) => {
                let mut a = self.clone();

                for ch in a.children_mut() {
                    match ch {
                        Child::Hole(i) => {
                            ex(*i).extract(ex, out);
                            *ch = Child::Hole(out.len() - 1);
                        }
                        Child::Constant(c) => {
                            out.push(Node::ConstInt(c.clone()));
                            *ch = Child::Constant(c.clone());
                        }
                        Child::VarInt(v) => {
                            out.push(Node::VarInt(*v));
                            *ch = Child::VarInt(v.clone());
                        }
                        Child::VarBool(v) => {
                            out.push(Node::VarBool(*v));
                            *ch = Child::VarBool(v.clone());
                        }
                    }
                }

                out.push(a);
            }
        });
    }
    cases
}

fn parse_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let symb  = &c.symb;
        let n     = c.argtys.len();
        cases.push(quote! {
            (#symb, s) if s.len() == #n => {
                let refs: ::std::vec::Vec<Child> = s.iter().map(|node| match node {
                    Node::PlaceHolder(i) => Child::Hole(*i),
                    Node::ConstInt(c)      => Child::Constant(*c),
                    Node::VarInt(v)      => Child::VarInt(*v),
                    Node::VarBool(v)     => Child::VarBool(*v),
                    _ => panic!("Expected PlaceHolder or Var*, got {:?}", node),
                }).collect();
                let refs: [Child; #n] = refs.try_into().unwrap();
                Some(Node::#ident(refs))
            }
        });
    }
    cases
}

fn parse_prod_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident    = &c.ident;
        let template = &c.template;
        let n        = c.argtys.len();
        cases.push(quote! {
            (#template, s) if s.len() == #n && #template == op => {
                let refs: ::std::vec::Vec<Child> = s.iter().map(|node| match node {
                    Node::PlaceHolder(i) => Child::Hole(*i),
                    Node::ConstInt(c)    => Child::Constant(*c),
                    Node::VarInt(v)      => Child::VarInt(*v),
                    Node::VarBool(v)     => Child::VarBool(*v),
                    _ => panic!("Expected PlaceHolder or Var*, got {:?}", node),
                }).collect();
                let refs: [Child; #n] = refs.try_into().unwrap();
                Some(Node::#ident(refs))
            }
        });
    }
    cases
}

fn ident_cases(edef: &EnumDef) -> Vec<TokenStream2> {
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident = &c.ident;
        let v = quote! { Node::#ident(_) => stringify!(#ident) };
        cases.push(v);
    }
    cases
}
