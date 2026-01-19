"""
table 1: message = full config of cegraph is better than baseline, regardless of heyristic.

cvc5
egraph
us (incremental computation + keeping n programs) [size, expert, learned, random]
table 2: message = number of programs stored matters. only for size heuristic

us no incremental
us incremental winning
us incremental + n programs
graph1: uniquely solved visual compariso

graph2: time. cactus plot unless we come up with anything better (try scatter 1 v 1: cvc5 vs best us, various versions of us v us)

appendix table: current table 1.
"""

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import ListedColormap

from extract_data import *


def one_v_one(x, y, xl, yl):
    valid = x.notna() & y.notna()
    x_only = x.notna() & y.isna()
    y_only = x.isna() & y.notna()

    plt.scatter(x[valid], y[valid], label='Both solved', alpha=0.7)
    ax = plt.gca()
    plt.xscale('log')
    plt.yscale('log')

    lims = [min(ax.get_xlim()[0], ax.get_ylim()[0]), 
            max(ax.get_xlim()[1], ax.get_ylim()[1])]

    for xi in x[x_only]:
        ax.add_patch(mpatches.Rectangle((xi*0.9, lims[0]), xi*0.2, lims[0]*0.1, 
                                        color='C1', alpha=0.7))
    for yi in y[y_only]:
        ax.add_patch(mpatches.Rectangle((lims[0], yi*0.9), lims[0]*0.1, yi*0.2,
                                        color='C2', alpha=0.7))

    ax.plot(lims, lims, 'k--', alpha=0.75, zorder=0)
    ax.set_aspect('equal')
    ax.set_xlim(lims)
    ax.set_ylim(lims)
    ax.set_xlabel(xl)
    ax.set_ylabel(yl)

    ax.legend(handles=[
        mpatches.Patch(color=f'C{i}', label=lbl, alpha=0.7)
        for i, lbl in enumerate(['Both solved', xl, yl])
    ])
    plt.show()


def cvb(b=None):
    df = get_lia_data() if b == 'lia' else get_rf_data()
    best = df.count().argmax()
    df = df.dropna(how='all')
    x, y = df['cvc5'], df.iloc[:, best]
    one_v_one(x, y, 'cvc5', df.columns[best])


def unique_solve(b=None):
    df = get_lia_data() if b == 'lia' else get_rf_data()
    df = df.drop(['r', 'r_w', 'r_wt'], axis=1)
    uc = df[df['cvc5'].notna() & (df.isnull().sum(axis=1) == len(df.columns) - 1)]
    uo = df[df['cvc5'].isna()]

    combined = pd.concat([uc, uo])

    matrix = np.zeros((len(combined), len(combined.columns)))
    matrix[:len(uc)] = uc.notna().astype(int)
    matrix[len(uc):] = uo.notna().astype(int) * 2

    fig, ax = plt.subplots(figsize=(14, 8), dpi=200)
    cmap = ListedColormap(['#FFFFFF', '#E74C3C', '#16A085']) 
    im = ax.imshow(matrix, cmap=cmap, aspect='auto', vmin=0, vmax=2, 
                   interpolation='nearest', alpha=0.9)

    ax.set_xticks(np.arange(len(combined.columns)), minor=False)
    ax.set_yticks(np.arange(len(combined)), minor=False)
    ax.set_xticks(np.arange(len(combined.columns)) - 0.5, minor=True)
    ax.set_yticks(np.arange(len(combined)) - 0.5, minor=True)
    ax.grid(which='minor', color='#CCCCCC', linestyle='-', linewidth=0.5)

    ax.set_xticklabels(combined.columns, rotation=45, ha='right', fontsize=10)
    ax.set_yticklabels(combined.index, fontsize=9)
    ax.set_xlabel('Solver', fontsize=10, fontweight='bold')
    ax.set_ylabel('Benchmarks', fontsize=10, fontweight='bold')

    plt.tight_layout()
    plt.show()


def not_solve(b=None):
    df = get_lia_data() if b == 'lia' else get_rf_data()
    df = df.drop(['r', 'r_w', 'r_wt'], axis=1)
    cs = df[df['cvc5'].notna() & (df.isnull().sum(axis=1) > 1)]

    matrix = np.zeros((len(cs), len(cs.columns)))
    matrix = cs.isna().astype(int)

    fig, ax = plt.subplots(figsize=(14, 8), dpi=200)
    cmap = ListedColormap(['#FFFFFF', '#F39C12']) 
    im = ax.imshow(matrix, cmap=cmap, aspect='auto', vmin=0, vmax=2, 
                   interpolation='nearest', alpha=0.9)

    ax.set_xticks(np.arange(len(cs.columns)), minor=False)
    ax.set_yticks(np.arange(len(cs)), minor=False)
    ax.set_xticks(np.arange(len(cs.columns)) - 0.5, minor=True)
    ax.set_yticks(np.arange(len(cs)) - 0.5, minor=True)
    ax.grid(which='minor', color='#CCCCCC', linestyle='-', linewidth=0.5)

    ax.set_xticklabels(cs.columns, rotation=45, ha='right', fontsize=10)
    ax.set_yticklabels(cs.index, fontsize=9)
    ax.set_xlabel('Solver', fontsize=10, fontweight='bold')
    ax.set_ylabel('Benchmarks', fontsize=10, fontweight='bold')

    plt.tight_layout()
    plt.show()
