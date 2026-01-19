import glob
import re
import statistics
import pandas as pd

from collections import defaultdict


com = re.compile(r'Completed (\d+).+')
ty = re.compile(r'.*\/grammar_(\w)(_(\w+))?')

lia = sorted(glob.glob('lia_results/*.txt'), key=lambda x: x[4:])
rf  = sorted(glob.glob('rf_results/*.txt'),  key=lambda x: x[3:])


get_com = lambda c: int(com.search(c.strip().split('\n')[-1]).group(1))


def get_avgtm(c, cvc=False):
    l = c.split('\n=')[1:]
    l[-1] = '\n'.join(l[-1].split()[:-2])
    if cvc:
        ts = [float(b.split()[-1][:-2]) / 1000 for b in l if 'define-fun' in b]
    else:
        ts = [float(b.split()[-1][:-2]) / 1000 for b in l if 'Answer' in b]
    return statistics.mean(ts), statistics.stdev(ts)


def get_inf(f):
    if 'cvc5' in f:
        return ('CVC5', 'CVC5', 'CVC5')
    elif 'egg' in f:
        return ('Egraph', 'Egraph', 'Egraph')
    else:
        m = ty.search(f)
        match m.groups():
            case (h, _, None):
                return ('CEgraph', h, None)
            case (h, _, i):
                return ('CEgraph', h, i)


d = defaultdict(lambda: defaultdict(dict))

for l, r in zip(lia, rf):
    a, b, c = get_inf(l)

    print(l)
    print(r)
    assert (a,b,c) == get_inf(r)

    with open(l, 'r') as f:
        lc = f.read()
    with open(r, 'r') as f:
        rc = f.read()

    lcom, rcom = get_com(lc), get_com(rc)
    lt, lsd = get_avgtm(lc, 'cvc5' in l)
    rt, rsd = get_avgtm(rc, 'cvc5' in r)

    d[a][b][c] = [lcom, lt, lsd, rcom, rt, rsd, lcom + rcom]


# -----------------------------
# build pandas table + CSV
# -----------------------------

rows = []

for algo, sub in d.items():
    for h, inner in sub.items():
        for i, vals in inner.items():
            lcom, lt, lsd, rcom, rt, rsd, tot = vals

            if algo in ("CVC5", "Egraph"):
                name = algo.lower()
            else:
                name = f"cegraph,{h}" if i is None else f"cegraph,{h},{i}"

            rows.append({
                "method": name,
                "#lia": lcom,
                "time lia": lt,
                "std lia": lsd,
                "#rf": rcom,
                "time rf": rt,
                "std rf": rsd,
                "total": tot,
            })

df = pd.DataFrame(rows).set_index("method")

# optional: stable ordering
order = ["cvc5", "egraph"]
order += sorted(m for m in df.index if m.startswith("cegraph"))
df = df.loc[order]

# optional: rounding
df = df.round({
    "time lia": 3,
    "std lia": 3,
    "time rf": 3,
    "std rf": 3,
})

df.to_csv("results_summary.csv")

def df_to_grouped_latex(df: pd.DataFrame, path: str = "results_summary.tex") -> str:
    x = df.copy()

    # ---- parse method index into (family, heuristic, variant) ----
    def split_method(m: str):
        if m in ("cvc5", "egraph"):
            return (m, "", "")
        # cegraph,d,wt  -> family=cegraph, heuristic=d, variant=wt
        parts = m.split(",")
        h = parts[1]
        v = "" if len(parts) == 2 else parts[2]
        return ("cegraph", h, v)

    idx = x.index.to_series().apply(split_method)
    x.index = pd.MultiIndex.from_tuples(idx.tolist(), names=["family", "heuristic", "variant"])

    # nice ordering
    family_order = ["cvc5", "egraph", "cegraph"]
    heuristic_order = ["", "d", "l", "r", "s"]
    variant_order = ["", "w", "wt"]

    x = x.sort_index()

    # Reindex to ensure proper ordering
    x = x.reindex(
        pd.MultiIndex.from_product(
            [family_order, heuristic_order, variant_order],
            names=["family", "heuristic", "variant"]
        )
    ).dropna(how='all')

    # replace empty strings with nicer symbols
    x = x.rename(index={"": "—"}, level="variant")
    x = x.rename(index={"": "—"}, level="heuristic")

    # ---- column grouping: LIA | RF | Total ----
    cols = pd.MultiIndex.from_tuples([
        ("LIA", r"\#"), ("LIA", "time"), ("LIA", "std"),
        ("RF",  r"\#"), ("RF",  "time"), ("RF",  "std"),
        ("Total", "total"),
    ])
    x.columns = cols

    formatters = {}
    for col in x.columns:
        if col[1] in [r"\#", "total"]:  # Integer columns
            formatters[col] = lambda val: f"{int(val)}" if pd.notna(val) else ""
        else:  # Float columns (time, std)
            formatters[col] = lambda val: f"{val:.2f}" if pd.notna(val) else ""

    # ---- LaTeX export ----
    # Add @{\hspace{1em}} for extra spacing between columns
    column_format = r"l@{\hspace{1em}}l@{\hspace{1em}}l|r@{\hspace{1em}}r@{\hspace{1em}}r|r@{\hspace{1em}}r@{\hspace{1em}}r|r"
    latex = x.to_latex(
        multicolumn=True,
        multirow=False,  # Disable automatic multirow to avoid mangling
        index=True,
        escape=False,
        column_format=column_format,
        caption="Benchmark summary (mean runtime in seconds; std is standard deviation).",
        formatters=formatters,
        label="tab:results_summary",
    )

    # ---- Post-process for manual multirow and better spacing ----
    lines = latex.split('\n')

    # First pass: count cegraph rows
    cegraph_count = sum(1 for line in lines if 'cegraph &' in line)

    new_lines = []
    cegraph_seen = 0
    current_heuristic_rows = 0

    for i, line in enumerate(lines):
        # Add spacing and configuration after \begin{table}
        if '\\begin{table}' in line:
            new_lines.append(line)
            new_lines.append('\\centering')
            new_lines.append('\\renewcommand{\\arraystretch}{1.3}')
            new_lines.append('\\setlength{\\tabcolsep}{8pt}')  # Additional column spacing
            continue

        # Add spacing after \toprule
        if '\\toprule' in line:
            new_lines.append(line)
            new_lines.append('\\addlinespace[0.5em]')
            continue

        # Handle cegraph rows with multirow
        if 'cegraph &' in line:
            cegraph_seen += 1

            if cegraph_seen == 1:
                # First cegraph row: insert \multirow only if there are multiple rows
                if cegraph_count > 1:
                    line = line.replace('cegraph &', f'\\multirow{{{cegraph_count}}}{{*}}{{cegraph}} &')
                # If only 1 row, keep it as-is
            else:
                # Subsequent cegraph rows: remove the family name
                line = line.replace('cegraph &', '&')

            # Track heuristic changes for cmidrule
            parts = line.split('&')
            if len(parts) > 2:
                variant = parts[2].strip()

                # If variant is 'wt', check if next line is different heuristic
                if variant == 'wt':
                    if i + 1 < len(lines):
                        next_line = lines[i + 1]
                        if 'cegraph &' in next_line or ('&' in next_line and next_line.strip().startswith('&')):
                            # Add cmidrule after this line
                            new_lines.append(line)
                            new_lines.append('\\cmidrule(lr){2-10}')
                            continue

        # Add spacing before \bottomrule
        if '\\bottomrule' in line:
            new_lines.append('\\addlinespace[0.5em]')
            new_lines.append(line)
            continue

        new_lines.append(line)

    latex_final = '\n'.join(new_lines)

    with open(path, "w") as f:
        f.write(latex_final)

    # return latex_final

# usage:
latex_str = df_to_grouped_latex(df, "results_summary.tex")
# print(latex_str)
