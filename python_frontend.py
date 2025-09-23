import sys
import sexpdata

from functools import partial
from dataclasses import dataclass
from collections import namedtuple
from itertools import chain
from more_itertools import partition


Arg = namedtuple('Arg', 'name, typ')
splitter = re.compile(r'[\(\)\s+]')

@dataclass
class ProductionRule:
    op  : str
    pr  : str
    _ret : str

    # yuck
    def extract_ret(self, nts):
        for n in nts:
            if self._ret == n.name:
                self.ret =  n.typ
                return

    # rough
    def extract_args(self, nts, varis):
        args = []
        for tok in splitter.split(self.pr):
            for n in chain(nts, varis):
                if tok == n.name:
                    args.append(n.typ)
        return args

    def extract_template(self, nts):
        tmp = self.pr
        for n in sorted(nts, key=lambda x: len(x.name), reverse=True):  # how ugly but needed
            tmp = tmp.replace(n.name, '?')
        return tmp

    def extract_eval(self, nts, varis, template):
        match self.ret:
            case 'Ty::Int' : r = "Value::Int"
            case 'Ty::Bool': r = "Value::Int"

        print(varis)
        ars = []
        count = 0
        for tok in splitter.split(self.pr):
            for x in chain(varis, nts):
                if tok == x.name:
                    match x.typ:
                        case 'Ty::Int': ars.append(f'to_int(ev({count})?)')
                        case 'Ty::Bool': ars.append(f'to_bool(ev({count})?)')
                    count += 1

        # TODO: Need to find a way to translate the operators to rust, will use some dictionary/regex it'll be ugly but whatever

        return f"{r}({' '.join(ars)})"


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
    args        : Arg
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

consume = lambda x: x.pop(0)
flat_map = lambda x: [a for a in x if a is not None]
flatflat_map = lambda x: [a for b in x for a in flat_map(b)]

def unpack_arg(x):
    n, t = x
    return Arg(n.value(), f'Ty::{t.value()}')

def get_args(s):
    args = []
    for x in s:
        args.append(unpack_arg(x))
    return args

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
        return Arg(s.value() if isinstance(s, sexpdata.Symbol) else s, nt.value())
    pr = get_pr(s)
    return ProductionRule(s[0].value(), pr, nt.value())

def get_prodrules(s):
    ret = consume(s)
    _ = consume(s)

    get_prodrule_nt = partial(get_prodrule, nt=ret)
    rules = map(get_prodrule_nt, consume(s))

    return rules

def parse_synth_fun(s):
    name = consume(s).value()
    args = get_args(consume(s))
    ret = consume(s).value()
    nonterms = get_args(consume(s))
    rules = flatflat_map(map(get_prodrules, consume(s)))

    prodrules, terminals = partition(lambda x: isinstance(x, Arg), rules)

    return SynthFun(name, args, ret, nonterms, list(terminals), list(prodrules))

def parse_define_fun(s):
    name = consume(s).value()
    args = get_args(consume(s))
    ret = consume(s)
    body = get_prodrule(consume(s), ret)

    return name, DefineFun(name, args, ret.value(), body)

def parse(sexprs):
    definefuns = {}
    for sxp in sexprs:
        match sxp[0].value():
            case 'synth-fun':
                synthfun = parse_synth_fun(sxp[1:])
            case 'define-fun':
                name, definefun = parse_define_fun(sxp[1:])
                definefuns[name] = define_fun
    return synthfun, definefuns


@dataclass
class GrammarTerm:
    name: str
    args: list[str]
    ret: str
    op: str
    tempalte: str
    evl: str

    def generate(self):
        return f"{self.name}, [{', '.join(self.args)}], {self.ret}, {self.op}, {self.template}, {self.evl}"

def extract_grammarterm(p, define_funs, nts, varis):
    p.extract_ret(nts)  # vile
    args     = p.extract_args(nts, varis)
    name     = op_map(p.op, len(args))
    ret      = p.ret
    op       = p.op
    template = p.extract_template(nts)
    evl      = p.extract_eval(nts, varis, template)

    return GrammarTerm(name, args, ret, op, template, evl)

def get_grammarterm(f=None):
    terms = []
    file = f if f else 'examples/max2_test.sl'
    with open(file, 'r') as f:
        sexprs = sexpdata.loads(f"({f.read()})")

    synthfun, definefuns =  parse(sexprs)

    for pr in synthfun.prodrules:
        term = extract_grammarterm(pr, definefuns, synthfun.nonterms, synthfun.args)
        print(term)
        terms.append(term)

get_grammarterm()
