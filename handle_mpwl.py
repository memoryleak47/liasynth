import sys

file = sys.argv[1]
with open(file) as f:
    lines = f.readlines()

consume = lambda l: l.pop(0)
apply_n = lambda f, x, n: [f(x) for _ in range(n)]
unpack_let = lambda l: apply_n(consume, l, 3)

def expand_lets(q):
    d = {}
    while q[0] == 'let':
        _, b, q = unpack_let(q)
        n, bod = b[0]
        d[n] = bod
    return d, q


def expand_nl(l, d):
    match l:
        case list():
            for i in range(len(l)):
                if isinstance(l[i], list):
                    expand_nl(l[i], d)
                elif isinstance(l[i], str) and (replacement := d.get(l[i])):
                    l[i] = replacement

def tokenize(l):
    l = l.replace("(", " ( ").replace(")", " ) ").strip()
    for i in range(10):
        l = l.replace("  ", " ")
    return l.split(" ")

def parse_r(toks):
    if toks[0] == "(":
        toks = toks[1:]
        l = []
        while toks[0] != ")":
            r, toks = parse_r(toks)
            l.append(r)
        return l, toks[1:]
    else:
        return toks[0], toks[1:]

def foo(ll, i, tab):
    l = ll[i]
    if type(l) != list:
        return
    for j in range(len(l)):
        foo(l, j, tab)
    if len(l) > 0 and l[0] == "move":
        j = len(tab)
        tab.append(l)
        ll[i] = "v" + str(j)

def fmt(p):
    if type(p) == str:
        return p
    if type(p) == list:
        p = [fmt(x) for x in p]
        return "(" + " ".join(p) + ")"

def op(l):
    toks = tokenize(l)
    p, [] = parse_r(toks)

    assert(len(p) == 2)
    assert(p[0] == "constraint")

    c, q = p
    import copy

    d, q = expand_lets(q)
    while True:
        prev = copy.deepcopy(q)
        expand_nl(q, d)
        if q == prev:
            break


    p = [c, q]
    tab = []
    foo(p, 1, tab)

    p = p[1]

    for i, t in enumerate(tab):
        v = "v" + str(i)
        print("(declare-var " + v + " Int)")
        p = ["=>", ["=", v, t], p]

    print(fmt(["constraint", p]))


for l in lines:
    if l.startswith("(constraint"):
        op(l)
    else:
        print(l)
