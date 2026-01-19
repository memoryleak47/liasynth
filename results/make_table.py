"""
table 1: message = full config of cegraph is better than baseline, regardless of heyristic.
    cvc5
    egraph
    us (incremental computation + keeping n programs) [size, expert, learned, random]
    no unique solved over cvc5

table 2: message = number of programs stored matters. only for size heuristic
    us no incremental
    us incremental winning
    us incremental + n programs

appendix table: current table 1.
"""

import pandas as pd


def make_latex_table(ldf_stats, rdf_stats, total_stats, columns, caption, filename):
    """Helper function to generate LaTeX table"""
    latex = []
    latex.append(r'\begin{table}[htbp]')
    latex.append(r'\centering')
    latex.append(r'\small')
    latex.append(r'\begin{tabular}{l|cc|cc|cc}')
    latex.append(r'\toprule')
    latex.append(r'\textbf{Solver} & \multicolumn{2}{c|}{\textbf{LIA}} & \multicolumn{2}{c|}{\textbf{Ranking Functions}} & \multicolumn{2}{c}{\textbf{Total}} \\')
    latex.append(r'& \textbf{Solved} & \textbf{Unique} & \textbf{Solved} & \textbf{Unique} & \textbf{Solved} & \textbf{Unique} \\')
    latex.append(r'\midrule')
    
    # Find maximum values for each column
    max_lia_solved = max(ldf_stats[s]['solved'] for s in columns)
    max_lia_unique = max(ldf_stats[s]['unique'] for s in columns if s != 'cvc5')
    max_rdf_solved = max(rdf_stats[s]['solved'] for s in columns)
    max_rdf_unique = max(rdf_stats[s]['unique'] for s in columns if s != 'cvc5')
    max_total_solved = max(total_stats[s]['solved'] for s in columns)
    max_total_unique = max(total_stats[s]['unique'] for s in columns if s != 'cvc5')
    
    def maybe_bold(value, max_value, is_unique=False):
        if is_unique and value == 0:
            return '--'
        val_str = str(value)
        if value == max_value:
            return r'\textbf{' + val_str + '}'
        return val_str
    
    for solver in columns:
        row = [solver]
        row.append(maybe_bold(ldf_stats[solver]['solved'], max_lia_solved))
        row.append(maybe_bold(ldf_stats[solver]['unique'], max_lia_unique, True) if solver != 'cvc5' else '--')
        row.append(maybe_bold(rdf_stats[solver]['solved'], max_rdf_solved))
        row.append(maybe_bold(rdf_stats[solver]['unique'], max_rdf_unique, True) if solver != 'cvc5' else '--')
        row.append(maybe_bold(total_stats[solver]['solved'], max_total_solved))
        row.append(maybe_bold(total_stats[solver]['unique'], max_total_unique, True) if solver != 'cvc5' else '--')
        latex.append(' & '.join(row) + r' \\')
    
    latex.append(r'\bottomrule')
    latex.append(r'\end{tabular}')
    latex.append(f'\\caption{{{caption}}}')
    latex.append(r'\label{tab:solver_comparison}')
    latex.append(r'\end{table}')
    
    latex_output = '\n'.join(latex)
    with open(filename, 'w') as f:
        f.write(latex_output)

def inc_summary():
    ld, rd = get_lia_data(), get_rf_data()
    ldf = ld[['cvc5', 's', 's_w', 's_wt']]
    rdf = rd[['cvc5', 's', 's_w', 's_wt']]
    ldf = ldf.rename({'s_wt': 'size-inc', 's_w': 'size-win', 's': 'size'}, axis=1)
    rdf = rdf.rename({'s_wt': 'size-inc', 's_w': 'size-win', 's': 'size'}, axis=1)

    def compute_stats(df):
        stats = {}
        for col in df.columns:
            solved = df[col].notna().sum()
            if col != 'cvc5':
                unique = ((df[col].notna()) & (df['cvc5'].isna())).sum()
                stats[col] = {'solved': solved, 'unique': unique}
        return stats

    ldf_stats = compute_stats(ldf)
    rdf_stats = compute_stats(rdf)

    total_stats = {}
    for col in ldf.columns:
        solved = ldf[col].notna().sum() + rdf[col].notna().sum()
        if col != 'cvc5':
            unique = (((ldf[col].notna()) & (ld['cvc5'].isna())).sum() + 
                     ((rdf[col].notna()) & (rd['cvc5'].isna())).sum())
            total_stats[col] = {'solved': solved, 'unique': unique}

    make_latex_table(
        ldf_stats, 
        rdf_stats, 
        total_stats, 
        ldf.columns.drop('cvc5'),
        'Number of benchmarks solved by incremental methods across LIA and Ranking Function datasets. Unique counts shows the number of benchmarks solved by a solver but not by cvc5.',
        'inc_sum_res.tex'
    )

def summary():
    ldf, rdf = get_lia_data(), get_rf_data()
    ldf = ldf[['cvc5', 'egraph', 's_wt', 'd_wt', 'l_wt', 'r_wt']]
    rdf = rdf[['cvc5', 'egraph', 's_wt', 'd_wt', 'l_wt', 'r_wt']]
    ldf = ldf.rename({'s_wt': 'size-inc', 'd_wt': 'expert-inc', 'l_wt': 'learned-inc', 'r_wt': 'random-inc'}, axis=1)
    rdf = rdf.rename({'s_wt': 'size-inc', 'd_wt': 'expert-inc', 'l_wt': 'learned-inc', 'r_wt': 'random-inc'}, axis=1)
    
    def compute_stats(df):
        stats = {}
        for col in df.columns:
            solved = df[col].notna().sum()
            if col != 'cvc5':
                unique = ((df[col].notna()) & (df['cvc5'].isna())).sum()
            else:
                unique = 0
            stats[col] = {'solved': solved, 'unique': unique}
        return stats
    
    ldf_stats = compute_stats(ldf)
    rdf_stats = compute_stats(rdf)
    
    total_stats = {}
    for col in ldf.columns:
        solved = ldf[col].notna().sum() + rdf[col].notna().sum()
        if col != 'cvc5':
            unique = (((ldf[col].notna()) & (ldf['cvc5'].isna())).sum() + 
                     ((rdf[col].notna()) & (rdf['cvc5'].isna())).sum())
        else:
            unique = 0
        total_stats[col] = {'solved': solved, 'unique': unique}
    
    make_latex_table(
        ldf_stats,
        rdf_stats,
        total_stats,
        ldf.columns,
        'Number of benchmarks solved by solver across LIA and Ranking Function datasets. Unique counts shows the number of benchmarks solved by a solver but not by cvc5.',
        'sum_res.tex'
    )
