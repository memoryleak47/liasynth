import os
import re
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

b_pat = re.compile(r'.*examples\/LIA\/(.*).sl')

def get_type(bench):
    with open(f"../examples/LIA/{bench}.sl", "r") as f:
        m = re.search(r'\(synth-fun .*?\)\s+(\w+)', f.read())
    return m.group(1) if m else None

bens = {}
all_benchmarks = set()

for file in os.listdir("."):
    if not file.endswith(".txt"):
        continue
    method = file[:-4]
    with open(file, "r") as f:
        benchs = f.read().split("==========")[1:]
    bs = [b_pat.search(b).group(1) for b in benchs]
    sols = [("Answer" in b or "define-fun" in b) for b in benchs]
    all_benchmarks.update(bs)
    bens[method] = {b: int(s) for b, s in zip(bs, sols)}

df = pd.DataFrame.from_dict(bens, orient="columns").fillna(0).astype(int)
df.index.name = "benchmark"

df["type"] = pd.Series({b: get_type(b) for b in df.index})


def create_heatmap_and_performance(df, title="All Benchmarks"):
    """
    Create a heatmap showing which methods solve which benchmarks + performance bars
    """
    methods = [c for c in df.columns if c != "type"]

    # Sort benchmarks by number of methods that solve them (ascending)
    df_sorted = df.copy()
    df_sorted['n_solved'] = df_sorted[methods].sum(axis=1)
    df_sorted = df_sorted.sort_values('n_solved', ascending=True)

    # Create figure with two subplots
    fig, (ax_heat, ax_method) = plt.subplots(1, 2, figsize=(18, max(12, len(df_sorted)*0.15)),
                                              gridspec_kw={'width_ratios': [3, 1]})

    # === HEATMAP: Each benchmark vs each method ===
    # Create matrix and color coding
    matrix = df_sorted[methods].values.astype(float)

    # Create RGB matrix for custom coloring
    # White = not solved, Black = solved (but not unique), Orange = only method to solve this benchmark
    rgb_matrix = np.ones((len(df_sorted), len(methods), 3))

    for i in range(len(df_sorted)):
        n_solving = int(matrix[i].sum())  # How many methods solve this benchmark
        for j in range(len(methods)):
            if matrix[i, j] == 1:
                # This method solves the benchmark
                if n_solving == 1:
                    # Orange: this is the ONLY method that solves this benchmark
                    rgb_matrix[i, j] = [1.0, 0.5, 0.0]  # Orange
                else:
                    # Black: solved, but other methods also solve it
                    rgb_matrix[i, j] = [0.2, 0.2, 0.2]  # Dark gray (softer than pure black)
            else:
                # White: not solved
                rgb_matrix[i, j] = [0.98, 0.98, 0.98]  # Off-white

    # Plot heatmap
    im = ax_heat.imshow(rgb_matrix, aspect='auto', interpolation='nearest')

    # Set ticks with better sizing
    ax_heat.set_xticks(np.arange(len(methods)))
    ax_heat.set_xticklabels([m.replace('grammar_', '').replace('_bench', '') for m in methods],
                            rotation=45, ha='right', fontsize=10, fontweight='bold')
    ax_heat.set_yticks(np.arange(len(df_sorted)))
    ax_heat.set_yticklabels(df_sorted.index, fontsize=7)

    # Add subtle grid
    for i in range(len(df_sorted) + 1):
        ax_heat.axhline(i - 0.5, color='#cccccc', linewidth=0.5, alpha=0.5)
    for i in range(len(methods) + 1):
        ax_heat.axvline(i - 0.5, color='#999999', linewidth=0.8, alpha=0.7)

    # Add title and labels
    ax_heat.set_xlabel('Methods', fontsize=11, fontweight='bold', labelpad=8)
    ax_heat.set_ylabel('Benchmarks', fontsize=11, fontweight='bold', labelpad=8)
    ax_heat.set_title(f'{title}\nWhite = Unsolved  |  Dark Gray = Solved  |  Orange = Unique Solver',
                     fontsize=12, fontweight='bold', pad=15)

    # Add checkmarks for smaller datasets
    if len(df_sorted) <= 60:
        for i in range(len(df_sorted)):
            n_solving = int(matrix[i].sum())
            for j in range(len(methods)):
                if matrix[i, j] == 1:
                    symbol = '✓'
                    if n_solving == 1:
                        color = 'white'  # White check on orange
                    else:
                        color = 'white'  # White check on dark gray
                    ax_heat.text(j, i, symbol, ha="center", va="center",
                               color=color, fontsize=7, fontweight='bold')

    # === METHOD PERFORMANCE BARS ===
    # FIX: Use df_sorted instead of df for counting
    method_counts = []
    for method in methods:
        solved = df_sorted[method].sum()  # Changed from df[method] to df_sorted[method]
        method_counts.append(solved)

    # Sort by performance
    method_data = list(zip(methods, method_counts))
    method_data.sort(key=lambda x: x[1], reverse=True)
    sorted_methods = [m for m, _ in method_data]
    sorted_counts = [c for _, c in method_data]

    method_names_short = [m.replace('grammar_', '') for m in sorted_methods]
    y_pos = np.arange(len(methods))

    # Color bars by performance
    colors_perf = ['#10b981' if c/len(df_sorted) > 0.7 else
                   '#f59e0b' if c/len(df_sorted) > 0.4 else
                   '#ef4444' for c in sorted_counts]

    ax_method.barh(y_pos, sorted_counts, color=colors_perf, alpha=0.7, edgecolor='black', linewidth=1.5)
    ax_method.set_yticks(y_pos)
    ax_method.set_yticklabels(method_names_short, fontsize=11, fontweight='bold')
    ax_method.set_xlabel('Total Benchmarks Solved', fontsize=13, fontweight='bold')
    ax_method.set_title('Individual Method Performance (sorted by performance)',
                       fontsize=12, fontweight='bold')
    ax_method.grid(axis='x', alpha=0.3, linestyle='--')
    ax_method.set_xlim(0, len(df_sorted) * 1.2)

    # Add detailed labels on bars - FIX: use df_sorted
    for i, (count, method) in enumerate(zip(sorted_counts, sorted_methods)):
        percentage = 100 * count / len(df_sorted)  # Changed from len(df)
        ax_method.text(count + len(df_sorted)*0.01, i,  # Changed from len(df)
                      f'{count}/{len(df_sorted)} ({percentage:.1f}%)',  # Changed from len(df)
                      va='center', fontsize=10, fontweight='bold')

    plt.tight_layout()
    plt.savefig(title, format='pdf')
    return fig, df_sorted

# Assuming your dataframe is called 'df'
# df = your_dataframe

# Create plots for each type
fig_all, sorted_all = create_heatmap_and_performance(df, "All Benchmarks")

fig_int, sorted_int = create_heatmap_and_performance(
    df[df['type'] == 'Int'], "Int Benchmarks")

fig_bool, sorted_bool = create_heatmap_and_performance(
    df[df['type'] == 'Bool'], "Bool Benchmarks")

plt.show()
