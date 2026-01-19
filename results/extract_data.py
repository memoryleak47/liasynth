import os
import re
import glob

import pandas as pd
from itertools import zip_longest
from collections import defaultdict


f_pat = re.compile(r'\/(\w+)\.sl')
f2_pat = re.compile(r'\/(\w+)\.noassumptions\.sl')
m_pat = re.compile(r'grammar_(\w+)\.txt')
o_pat = re.compile(r'(\w+)\.txt')

def me(f):
    if (m := m_pat.search(f)):
        return m.group(1)
    return o_pat.search(f).group(1)

def get_solved(file, d, b):
    flag = 'define-fun' if 'cvc5' in file else 'Answer'
    p = f2_pat if b == 'rf' else f_pat

    with open(file, 'r') as f: content = f.read()
    l = content.split('\n=')[1:]
    l[-1] = '\n'.join(l[-1].split()[:-2])
    bs = [p.search(b.split()[2]).group(1) for b in l]
    ts = [float(b.split()[-1][:-2])/1000 if flag in b else None for b in l]

    for b, t in zip(bs, ts):
        d[b].append(t)

def get_df(fs, columns, b):
    d = defaultdict(list)
    for f in fs: get_solved(f, d, b)
    df = pd.DataFrame(d).T
    df.index = list(d.keys())
    df.columns = list(columns)
    return df.dropna(how='all')

def get_lia_data():
    fs = sorted(glob.glob('lia_results/*.txt'), key=lambda x: x[4:])
    columns = map(me, fs)
    return get_df(fs, columns, 'lia')


def get_rf_data():
    fs = sorted(glob.glob('rf_results/*.txt'),  key=lambda x: x[3:])
    columns = map(me, fs)
    return get_df(fs, columns, 'rf')
