import sys
import re
import sexpdata
import copy

from functools import partial
from dataclasses import dataclass
from collections import namedtuple, defaultdict
from itertools import chain
from more_itertools import partition


Arg = namedtuple('Arg', 'name, typ')
Nt = namedtuple('Nt', 'name, typ, t')
splitter = re.compile(r'([\(\)\s+])')
spaces = re.compile(r'\s+')
consume = lambda x: x.pop(0)
flat_map = lambda x: [a for a in x if a is not None]
flatflat_map = lambda x: [a for b in x for a in flat_map(b)]
apply_n = lambda f, x, n: [f(x) for _ in range(n)]
compose = lambda f, g: lambda x: f(g(x))


@dataclass
class GrammarTerm:
    name: str
    args: list[str]
    ret: str
    op: str
    template: str
    evl: str

    def __hash__(self):
        return hash(self.template)

    def __eq__(self, other):
        return self.template == other.template

    def generate(self):
        return f'({self.name}, [{', '.join(self.args)}], Ty::{self.ret}, "{self.op}", "{self.template}", {self.evl})'


needed_terms = {
    GrammarTerm('Not',      ['Ty::Bool'], 'Bool', "not", "(not ?)", 'Value::Bool(!to_bool(ev(0)?))'),
    GrammarTerm('Implies',  ['Ty::Bool', 'Ty::Bool'], 'Bool', "=>", "(=> ? ?)", 'Value::Bool(!to_bool(ev(0)?) || to_bool(ev(1)?))'),
    GrammarTerm('And',      ['Ty::Bool', 'Ty::Bool'], 'Bool', "and", "(and ? ?)", 'Value::Bool(to_bool(ev(0)?) && to_bool(ev(1)?))'),
    GrammarTerm('Or',       ['Ty::Bool', 'Ty::Bool'], 'Bool', "or", "(or ? ?)", 'Value::Bool(to_bool(ev(0)?) || to_bool(ev(1)?))'),
    GrammarTerm('Xor',      ['Ty::Bool', 'Ty::Bool'], 'Bool', "xor", "(xor ? ?)", 'Value::Bool(to_bool(ev(0)?) != to_bool(ev(1)?))'),
    GrammarTerm('Equals',   ['Ty::Int', 'Ty::Int'], 'Bool', "=", "(= ? ?)", 'Value::Bool(ev(0)? == ev(1)?)'),
    GrammarTerm('Distinct', ['Ty::Int', 'Ty::Int'], 'Bool', "distinct", "(distinct ? ?)", 'Value::Bool(ev(0)? != ev(1)?)'),
    GrammarTerm('Ite',      ['Ty::Bool', 'Ty::Int', 'Int'], 'Ty::Int', "ite", "(ite ? ? ?)", 'Value::Int(if to_bool(ev(0)?) { ev(1)? } else { ev(2)? })'),

    GrammarTerm('Neg',      ['Ty::Int'], 'Int', "-", "(- ?)", 'Value::Int(-to_int(ev(0)?))'),
    GrammarTerm('Sub',      ['Ty::Int', 'Ty::Int'], 'Int', "-", "(- ? ?)", 'Value::Int(to_int(ev(0)?) - to_int(ev(1)?))'),
    GrammarTerm('Add',      ['Ty::Int', 'Ty::Int'], 'Int', "+", "(+ ? ?)", 'Value::Int(to_int(ev(0)?) + to_int(ev(1)?))'),
    GrammarTerm('Mul',      ['Ty::Int', 'Ty::Int'], 'Int', "*", "(* ? ?)", 'Value::Int(to_int(ev(0)?) * to_int(ev(1)?))'),
    GrammarTerm('Div',      ['Ty::Int', 'Ty::Int'], 'Int', "div", "(div ? ?)", '{let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) / to_int(b)) }}'),
    GrammarTerm('Mod',      ['Ty::Int', 'Ty::Int'], 'Int', "mod", "(mod ? ?)", '{ let b = ev(1)?; if b == Value::Int(0) { return None } else { Value::Int(to_int(ev(0)?) % to_int(b)) }}'),
    GrammarTerm('Abs',      ['Ty::Int'], 'Int', "abs", "(abs ?)", 'Value::Int(to_int(ev(0)?).abs())'),

    GrammarTerm('Lte', ['Ty::Int', 'Ty::Int'], 'Bool', "<=", "(<= ? ?)", 'Value::Bool(to_int(ev(0)?) <= to_int(ev(1)?))'),
    GrammarTerm('Lt', ['Ty::Int', 'Ty::Int'], 'Bool', "<", "(< ? ?)", 'Value::Bool(to_int(ev(0)?) < to_int(ev(1)?))'),
    GrammarTerm('Gte', ['Ty::Int', 'Ty::Int'], 'Bool', ">=", "(>= ? ?)", 'Value::Bool(to_int(ev(0)?) >= to_int(ev(1)?))'),
    GrammarTerm('Gt', ['Ty::Int', 'Ty::Int'], 'Bool', ">", "(> ? ?)", 'Value::Bool(to_int(ev(0)?) > to_int(ev(1)?))'),
}


@dataclass
class ProductionRule:
    op  : str
    pr  : str
    sexp: list
    ret : Arg

    # rough
    def extract_args(self, nts):
        args = []
        self.a_idx = []
        idx = 0
        seen = {}
        for tok in splitter.split(self.pr):
            for n in nts:
                if tok.strip() == n.name:
                    args.append(n.typ)
                    self.a_idx.append(idx)
                    idx += 1
            for v in self.varis:
                if tok.strip() == v.name:
                    args.append(v.typ)
                    if (i := seen.get(v.name)) is not None:
                        self.a_idx.append(i)
                    else:
                        self.a_idx.append(idx)
                        seen[v.name] = idx
                        idx += 1
        return args

    def extract_template(self, nts):
        tmp = self.pr
        for n in sorted(nts, key=lambda x: len(x.name), reverse=True):  # how ugly but needed
            tmp = tmp.replace(n.name, '?')

        return tmp

    def get_a_idx(self):
        for tok in splitter.split(self.pr):
            for n in chain(nts, varis):
                if tok == n.name:
                    args.append(n.typ)

    def extract_eval(self, nts, template, deffuns):
        match self.ret:
            case (_, 'Int') : r = "Value::Int"
            case (_, 'Bool'): r = "Value::Bool"

        tmp = self.sexp
        tmp = replace(tmp, nts, self.varis, deffuns, self.a_idx)
        return f"{r}{get_rust_eval(tmp)}"


def replace(tmp, nts, varis, deffuns, a_idx):
    idxs = iter(range(len(tmp)))
    for i in idxs:
        t = tmp[i]
        match t:
            case [*ts]:
                tmp[i] = replace(ts, nts, varis, deffuns, a_idx)

            case _ if (d := deffuns.get(t.strip())) is not None:
                d = copy.deepcopy(d)
                pr = d.body
                pr.varis = d.args
                d_aidx = apply_n(consume, a_idx, len(d.args))
                pr.extract_args(nts)
                a_idx = [d_aidx[j] for j in pr.a_idx]
                t = replace(pr.sexp, nts, pr.varis, deffuns, a_idx)
                tmp[i] = get_rust_eval(t)

                for _ in range(len(d.args)):
                    next(idxs, None)

            case _:
                for x in chain(varis, nts):
                    if t.strip() == x.name:
                        idx = consume(a_idx)
                        rep = f"to_int(ev({idx})?)" if x.t == "Int" else f"to_bool(ev({idx})?)"
                        tmp[i] = rep
                        break
                else:
                    match t:
                        case sexpdata.Symbol(t): tmp[i] = t.value()
                        case _: tmp[i] = t
    return tmp

rust_diad = lambda o, x, y:  f"({x} {o} {y})"
rust_mon = lambda o, x:  f"({o} {x})"
rust_imply = lambda x, y: f"(!{x} || {y})"
rust_ite = lambda c, x, y: f"(if {c} {{ {x} }} else {{ {y} }} )"
rust_div = lambda n, x, y: f"({{let b = ev(1)?; if b== Value::Int(0) {{ return None }} else {{ {x} {n} to_int(b) }} }})"

rust_boolean = {
    'not'     : '!',
    'and'     : '&&',
    'or'      : '||',
    'xor'     : '!=',
    '='       : '==',
    'distinct': '!=',
}

rust_div_mod = {
    'div': r'/',
    'div': r'%',
}

def get_rust_eval(s):
    if not isinstance(s, list):
        return s
    match (n := consume(s)):
        case [term]: return get_rust_eval(term)
        case '-' if len(s) == 1:
                return rust_mon(n, *apply_n(compose(get_rust_eval, consume), s, 1))
        case '+' | '-' | '*' | '<=' | '<' | '>' | '>=':
            return rust_diad(n, *apply_n(compose(get_rust_eval, consume), s, 2))
        case 'not':
            return rust_mon(rust_boolean[n], *apply_n(compose(get_rust_eval, consume), s, 1))
        case 'and' | 'or' | 'xor' | '=':
            return rust_diad(rust_boolean[n], *apply_n(compose(get_rust_eval, consume), s, 2))
        case 'div' | 'mod':
            return rust_div(rust_div_mod[n], *apply_n(compose(get_rust_eval, consume), s, 2))
        case '=>':
            return rust_imply(n, *apply_n(compose(get_rust_eval, consume), s, 2))
        case 'ite':
            return rust_ite( *apply_n(compose(get_rust_eval, consume), s, 3))
        case _:
            return n


@dataclass
class SynthFun:
    name        : str
    args        : Arg
    ret         : str
    nonterms    : list[Arg]
    terminals   : list[Arg]
    prodrules  : list[ProductionRule]

@dataclass
class DefineFun:
    name        : str
    args        : list[Arg]
    ret         : str
    body        : ProductionRule

def op_map(op, na):
    match op, na:
        case ('=>', _):  return 'Implies'
        case ('=', _):   return 'Equals'
        case ('-', 1):   return 'Neg'
        case ('-', _):   return 'Sub'
        case ('+', _):   return 'Add'
        case ('*', _):   return 'Mul'
        case ('<=', _):  return 'Lte'
        case ('<', _):   return 'Lt'
        case ('>=', _):  return 'Gte'
        case ('>', _):   return 'Gt'
        case _: return op.capitalize()

def get_args(s):
    args = []
    for x in s:
        n, t = x
        args.append(Arg(n.value(), f'Ty::{t.value()}'))
    return args

def get_nont(s):
    nts = []
    for i, x in enumerate(s):
        n, t = x
        nts.append(Nt(n.value(), f'Ty::NonTerminal({i})', t.value()))
    return nts

# BUG: This fails sometimes, need to sort
def get_pr(p):
    pr = "("
    for i, e in enumerate(p):
        if isinstance(e, list):
            pr += " "
            pr += get_pr(e)
        else:
            if i != 0: pr += " "
            pr += e.value()
    pr += ")"
    return pr

def get_prodrule(s, nt):
    if not isinstance(s, list):
        return Arg(s.value() if isinstance(s, sexpdata.Symbol) else s, nt)
    pr = get_pr(s)
    return ProductionRule(s[0].value(), pr, s, nt)

def get_prodrules(s):
    ret = (consume(s).value(), consume(s).value())

    get_prodrule_nt = partial(get_prodrule, nt=ret)
    rules = map(get_prodrule_nt, consume(s))

    return rules

def parse_synth_fun(s):
    name = consume(s).value()
    args = get_args(consume(s))
    ret = consume(s).value()
    nonterms = get_nont(consume(s))
    ret = nonterms[0]
    rules = flatflat_map(map(get_prodrules, consume(s)))

    prodrules, terminals = partition(lambda x: isinstance(x, Arg), rules)

    return SynthFun(name, args, ret, nonterms, list(terminals), list(prodrules))

def parse_define_fun(s, defnum):
    name = consume(s).value()
    args = get_args(consume(s))
    ret = consume(s)
    body = get_prodrule(consume(s), ret)

    return name, DefineFun(name, args, ret.value(), body)

def parse(sexprs):
    definefuns = {}
    defnum = 0
    for sxp in sexprs:
        match sxp[0].value():
            case 'synth-fun':
                synthfun = parse_synth_fun(sxp[1:])
            case 'define-fun':
                name, definefun = parse_define_fun(sxp[1:], defnum)
                definefuns[name] = definefun
    return synthfun, definefuns


def extract_grammarterm(p, definefuns, nts, deffs={}):
    args     = p.extract_args(nts)
    name     = op_map(p.op, len(args))
    ret      = p.ret[0]
    op       = p.op
    template = p.extract_template(nts)
    evl      = p.extract_eval(nts, template, deffs)

    return GrammarTerm(name, args, ret, op, template, evl)

def get_grammarterm(file=None):
    with open(file, 'r') as f:
        sexprs = sexpdata.loads(f"({f.read()})")

    synthfun, definefuns =  parse(sexprs)
    defnum = 0

    terms = set()
    names = defaultdict(int)
    for pr in synthfun.prodrules:
        pr.varis = synthfun.args
        term = extract_grammarterm(pr, definefuns, synthfun.nonterms, definefuns)
        term.name = term.name.replace('-', '')
        if names.get(term.name) is not None:
            term.name += str(names[term.name])
            names[term.name] += 1
        if term.ret not in ['Int', 'Bool']:
            idx ,= [i for i, n in enumerate(synthfun.nonterms) if n.name == term.ret]
            term.ret = f'NonTerminal({idx})'
        terms.add(term)

    extra = needed_terms.difference(terms)
    return terms.union(extra)

def langfile(f):
    terms = get_grammarterm(f)
    sterms = ',\n\t\t'.join(t.generate() for t in terms)

    with open('src/langdef.rs', 'w') as f:
        f.write(f"""use crate::*;
use lang::define_language;

define_language! {{
    [
        {sterms}
    ]
}}
        """)


if len(sys.argv) < 2:
    f = 'examples/LIA/max2.sl'
else:
    f = sys.argv[1]
langfile(f)
