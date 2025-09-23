import sys
import sexpdata

from functools import partial
from dataclasses import dataclass
from collections import namedtuple
from more_itertools import partition


Arg = namedtuple('Arg', 'name, type')

@dataclass
class ProductionRule:
    pr  : str
    ret : str

    def extract_args(self, nts):
        ...

    def extract_template(self, nts):
        ...

    def extract_eval(self):
        ...

@dataclass
class SynthFun:
    name        : str
    args        : Arg
    ret         : str
    nonterms    : Arg
    terminals   : list[Arg]
    prodrules  : list[ProductionRule]

@dataclass
class DefineFun:
    name        : str
    args        : Arg
    ret         : str
    body        : ProductionRule

consume = lambda x: x.pop(0)
flat_map = lambda x: [a for a in x if a is not None]
flatflat_map = lambda x: [a for b in x for a in flat_map(b)]
splitter = re.compile(r'[\(\)\s+]')

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
    return ProductionRule(pr, nt.value())

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

    return SynthFun(
        name,
        args,
        ret,
        nonterms,
        list(terminals),
        list(prodrules),
    )

def parse_define_fun(s):
    name = consume(s).value()
    args = get_args(consume(s))
    ret = consume(s)
    body = get_prodrule(consume(s), ret)

    return name, DefineFun(
        name,
        args,
        ret.value(),
        body
    )

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

def get_custom_grammar(f=None):
    file = f if f else 'examples/max2_test.sl'
    with open(file, 'r') as f:
        sexprs = sexpdata.loads(f"({f.read()})")

    synthfun, definefuns =  parse(sexprs)
