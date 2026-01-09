import os
import re

import pandas as pd
from collections import defaultdict
import matplotlib.pyplot as plt
import numpy as np
import colorsys


f_pat = re.compile(r'\/(\w+)\.sl')
m_pat = re.compile(r'grammar_(\w+)\.txt')

h_map = {
    'd': 'd',
    'r': 'r',
    's': 's',
    'l': 'l'
}

i_map = {
    'w': 'w',
    'wt': 'w-m'
}

def meth_map(f):
    m = m_pat.search(f).group(1)
    h, *rest = m.split('_', 1)
    if rest:
        return (h_map[h], i_map[rest[0]])
    return (h_map[h], 'no')

d = defaultdict(list)

for file in os.listdir():
    if file.endswith('.txt'):
        with open(file, 'r') as f: content = f.read()
        l = content.split('\n=')[1:]
        l[-1] = '\n'.join(l[-1].split()[:-2])
        bs = [f_pat.search(b.split()[2]).group(1) for b in l]
        ts = [float(b.split()[-1][:-2])/1000 for b in l]

        d['bench'].extend(bs)
        d['times'].extend(ts)

        if 'grammar' in file:
            sol = ['Answer' in x for x in l]
            meth, inc = meth_map(file)
            d['heuristic'].extend([meth]*len(bs))
            d['incremental'].extend([inc]*len(bs))
        elif 'egg' in file:
            sol = ['Answer' in x for x in l]
            d['heuristic'].extend(["egraph"]*len(bs))
            d['incremental'].extend(["egraph"]*len(bs))
        else:
            sol = ['define-fun' in x for x in l]
            d['heuristic'].extend(['cvc5'] * len(bs))
            d['incremental'].extend(['cvc5'] * len(bs))
        d['solved'].extend(sol)

df = pd.DataFrame.from_dict(d)

def _adjust_lightness(color, factor):
    r, g, b, a = color
    h, l, s = colorsys.rgb_to_hls(r, g, b)
    l = max(0.0, min(1.0, l * factor))
    r2, g2, b2 = colorsys.hls_to_rgb(h, l, s)
    return (r2, g2, b2, a)


def cactus(
    df,
    gcols=("heuristic", "incremental"),
    time_col="times",
    solved_col="solved",
    jitter=0.12,
):
    plt.style.use("seaborn-v0_8-darkgrid")
    plt.rcParams.update({
        "font.size": 9,
        "axes.labelsize": 10,
        "axes.titlesize": 11,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "lines.linewidth": 1.9,
        "grid.linewidth": 0.5,
        "grid.alpha": 0.4,
    })

    d = df.copy()
    d = d[d[solved_col].astype(bool)].copy()

    heuristics = sorted(d[gcols[0]].unique().tolist())
    incrementals = sorted(d[gcols[1]].unique().tolist())

    # Base colors: one per heuristic (so configs with same heuristic "read" as a group)
    base_cmap = plt.get_cmap("tab10")
    base_colors = {h: base_cmap(i % base_cmap.N) for i, h in enumerate(heuristics)}

    # Within a heuristic, vary lightness by incremental type (same hue family)
    # You can tweak these multipliers if you have many incrementals.
    if len(incrementals) == 1:
        lightness = {incrementals[0]: 1.0}
    else:
        # spread factors around 1.0 (darker <1, lighter >1)
        factors = np.linspace(0.80, 1.25, num=len(incrementals))
        lightness = {inc: float(factors[i]) for i, inc in enumerate(incrementals)}

    # Stable order: group by heuristic, then incremental
    groups = []
    for h in heuristics:
        for inc in incrementals:
            g = d[(d[gcols[0]] == h) & (d[gcols[1]] == inc)]
            if len(g):
                groups.append(((h, inc), g))

    if not groups:
        raise ValueError("No solved rows to plot after filtering.")

    fig, ax = plt.subplots(figsize=(8, 6))

    endpoints = []
    max_y = 0

    # Draw: slight y-jitter per curve to avoid exact overlap
    for i, ((h, inc), g) in enumerate(groups):
        s = np.sort(g[time_col].to_numpy(dtype=float))
        s = s[np.isfinite(s) & (s > 0)]
        if s.size == 0:
            continue

        y = np.arange(1, s.size + 1)
        max_y = max(max_y, int(y[-1]))

        y = y + (i - (len(groups) - 1) / 2) * float(jitter)

        c = _adjust_lightness(base_colors[h], lightness[inc])

        ax.plot(
            s, y,
            color=c,
            alpha=0.92,
            solid_capstyle="round",
            zorder=2,
        )

        endpoints.append((s[-1], y[-1], h, inc, int(s.size), c))

    # Endpoint labels: clearer + include solved count
    # Place labels with a small multiplicative x-offset so they sit to the right on log scale.
    x_mult = 1.06

    for x, y, h, inc, nsolved, c in endpoints:
        label = f"{h}, {inc} (n={nsolved})"
        ax.text(
            x * x_mult,
            y,
            label,
            fontsize=8.5,
            fontweight="bold",
            ha="left",
            va="center",
            color=c,
            bbox=dict(boxstyle="round,pad=0.18", facecolor="white", edgecolor="none", alpha=0.75),
            zorder=5,
        )

    ax.set_xscale("log")
    ax.set_xlabel("Time (s)", fontweight="bold")
    ax.set_ylabel("Number of solved instances", fontweight="bold")
    ax.set_ylim(0, max_y * 1.05)

    ax.grid(True, which="major")
    ax.grid(True, which="minor", linestyle=":")

    plt.tight_layout()
    plt.savefig('cactus_plot.pdf', bbox_inches='tight')
    plt.savefig('cactus_plot.png', bbox_inches='tight', dpi=300)
    plt.show()
    print("Plots saved")


def get_table(df):
    df = df.round(2)
    df['config'] = df['heuristic'] + ['-' + x if x != 'no' else '' for x in df['incremental']]
    df['time_or_dash'] = df.apply(lambda row: row['times'] if row['solved'] else '-', axis=1)
    result = df.pivot_table(
        index='bench',
        columns='config',
        values='time_or_dash',
        aggfunc='first'  # In case there are duplicates, take the first value
    )
    result = result.reset_index()
    result = result.rename({
                           'cvc5-cvc5':     'cvc5',
                           'egraph-egraph': 'egraph'
                       }, axis=1)
    latex = result.to_latex(
        index=False,
        escape=True,
        longtable=True,
        caption="Results",
        label="tab:results",
        float_format="%.2f",
        column_format="l" + "r" * (len(result.columns)-1),
        bold_rows=False,
    )
    
    with open("results_table.tex", "w") as f:
        f.write(latex)


cactus(df)
# get_table(df)
