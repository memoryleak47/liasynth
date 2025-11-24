#!/usr/bin/python3 -B

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

    tab = []
    foo(p, 1, tab)

    p = p[1]

    for i, t in enumerate(tab):
        v = "v" + str(i)
        print("(declare-var " + v + " Int)")
        p = ["=>", ["=", v, t], p]

    print(fmt(["constraint", p]))

import sys
f = sys.argv[1]
lines = open(f).readlines()
for l in lines:
    if l.startswith("(constraint"):
        op(l)
    else:
        print(l)
