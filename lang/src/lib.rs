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

        #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, PartialOrd, Ord)]
        pub enum Child {
            Hole(Id),
            Constant(Int),
            VarInt(Var),
            VarBool(Var),
        }

		impl Child {
			pub fn into_id(&self) -> Option<Id> {
				match self {
					Self::Hole(id) => Some(*id),
					_ => None
				}
			}
		}

        #[derive(PartialEq, Eq, Hash, Clone, Debug, PartialOrd, Ord)]
        pub enum Node {
            PlaceHolder(Id, Ty),
            ConstInt(Int, Ty),
            True(Ty),
            False(Ty),
            VarInt(Var, Ty),
            VarBool(Var, Ty),
            #(#enum_cases),*
        }

        impl Node {
            pub fn signature(&self) -> (&'static [Ty], Ty) {
                match self {
                    Node::PlaceHolder(_, ty)  => (&[], *ty),
                    Node::ConstInt(_, ty) => (&[], *ty),
                    Node::True(ty)        => (&[], *ty),
                    Node::False(ty)       => (&[], *ty),
                    Node::VarInt(_, ty)   => (&[], *ty),
                    Node::VarBool(_, ty)  => (&[], *ty),
                    #(#signature_cases),*
                }
            }

            pub fn template(&self) -> Option<&'static str> {
                match self {
                    Node::PlaceHolder(_, _)
                    | Node::ConstInt(_, _)
                    | Node::True(_)
                    | Node::False(_)
                    | Node::VarInt(_, _)
                    | Node::VarBool(_, _) => None,
                    #(#template_cases),*
                }
            }

            pub fn children(&self) -> &[Child] {
                match self {
                    Node::PlaceHolder(_, _)
                    | Node::ConstInt(_, _)
                    | Node::True(_)
                    | Node::False(_)
                    | Node::VarInt(_, _)
                    | Node::VarBool(_, _) => &[] as &[Child],
                    #(#get_children_cases),*
                }
            }

            pub fn children_mut(&mut self) -> &mut [Child] {
                match self {
                    Node::PlaceHolder(_, _)
                    | Node::ConstInt(_, _)
                    | Node::True(_)
                    | Node::False(_)
                    | Node::VarInt(_, _)
                    | Node::VarBool(_, _) => &mut [] as &mut [Child],
                    #(#get_children_mut_cases),*
                }
            }

            pub fn eval(&self, ch: impl Fn(usize, Id) -> Option<Value>, sigma: &Sigma) -> Option<Value> {
                Some(match self {
                    Node::PlaceHolder(_, _) => Value::Int(0),
                    Node::ConstInt(i, _) => Value::Int(*i),
                    Node::True(_) => Value::Bool(true),
                    Node::False(_) => Value::Bool(false),
                    Node::VarInt(v, _) | Node::VarBool(v, _) => sigma.get(*v).unwrap_or_else(|| panic!("Failed {sigma:?} index with {v}")).clone(),
                    #(#eval_cases),*
                })
            }

            pub fn extract(&self,  ex: &impl Fn(usize, Id) -> Node, out: &mut Vec<Node>) {
                match self {
                    a@(Node::PlaceHolder(_, _) | Node::ConstInt(_, _) | Node::True(_) | Node::False(_) | Node::VarInt(_, _) | Node::VarBool(_, _)) => out.push(a.clone()),
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
                        println!("parse_prod: unknown op {:?}, args={:?}", op, args);
                        None
                    },

                }
            }

            pub fn ident(&self) -> &'static str {
                match self {
                    Node::PlaceHolder(_, _) => "PlaceHolder",
                    Node::ConstInt(_, _) => "ConstInt",
                    Node::True(_) => "True",
                    Node::False(_) => "False",
                    Node::VarInt(_, _)  => "VarInt",
                    Node::VarBool(_, _) => "VarBool",
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
    let mut cases = Vec::new();
    for c in edef.cases.iter() {
        let ident  = &c.ident;
        let retty  = &c.retty;
        let argtys = &c.argtys;

        // rvalue promotion gives this a 'static lifetime
        let args = quote! { &[#(#argtys),*] };

        cases.push(quote! {
            Node::#ident(_) => (#args, #retty)
        });
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
                let (argtys, _) = self.signature();
                let ev = |x: usize| -> Option<Value> {
                    match (&argtys[x], &s[x]) {
                        (&Ty::NonTerminal(j), &Child::Hole(i)) => ch(j, i),
                        (_,                   &Child::Hole(i)) => None,
                        (_,                   &Child::Constant(c)) => Some(Value::Int(c)),
                        (_,                   &Child::VarInt(v))   => Some(sigma.get(v).cloned().unwrap_or_else(|| panic!("sigma miss {v}"))),
                        (_,                   &Child::VarBool(v))  => Some(sigma.get(v).cloned().unwrap_or_else(|| panic!("sigma miss {v}"))),
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
                let (argtys, _) = a.signature();
                {
                    let chs = a.children_mut();
                    for i in 0..chs.len() {
                        match (&argtys[i], &mut chs[i]) {
                            (&Ty::NonTerminal(j), &mut Child::Hole(ref mut idx)) => {
                                ex(j, *idx).extract(ex, out);
                                *idx = out.len() - 1; 
                            }
                            (_,  &mut Child::Hole(ref mut idx)) => {}
                            (&ty, &mut Child::Constant(c)) => {
                                out.push(Node::ConstInt(c, ty));
                            }
                            (&ty, &mut Child::VarInt(v)) => {
                                out.push(Node::VarInt(v, ty));
                            }
                            (&ty, &mut Child::VarBool(v)) => {
                                out.push(Node::VarBool(v, ty));
                            }
                        }
                    }
                } // <- mutable borrow of `a` ends here

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
                    Node::PlaceHolder(i, _) => Child::Hole(*i),
                    Node::ConstInt(c, _)      => Child::Constant(*c),
                    Node::VarInt(v, _)      => Child::VarInt(*v),
                    Node::VarBool(v, _)     => Child::VarBool(*v),
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
                    Node::PlaceHolder(i, _) => Child::Hole(*i),
                    Node::ConstInt(c, _)    => Child::Constant(*c),
                    Node::VarInt(v, _)      => Child::VarInt(*v),
                    Node::VarBool(v, _)     => Child::VarBool(*v),
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
