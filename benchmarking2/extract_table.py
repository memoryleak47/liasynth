import os
import re
import pandas as pd

b_pat = re.compile(r'.*examples\/LIA\/(.*).sl')
t_pat = re.compile(r'\(synth-fun .*\) (.*)')

def get_type(file):
    file = f"../examples/LIA/{file}.sl"
    with open(file, 'r') as f:
        content = f.read()


    return t_pat.search(content).group(1)

bens = {}
for file in os.listdir("."):
    if file.endswith(".txt"):
        with open(os.path.join("", file), 'r') as f:
            content = f.read()
            benchs = content.split('==========')[1:]

            bs = [b_pat.search(b).group(1) for b in benchs]
            typs = [get_type(b) for b in bs]
            sol = ["Answer" in b or "define-fun" in b for b in benchs]
            bens[file[:-4]] = sol

df = pd.DataFrame.from_dict(bens)
df['type'] = typs
df.index = bs

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Rectangle

def create_heatmap_and_performance(df, title="All Benchmarks"):
    """
    Create a heatmap showing which methods solve which benchmarks + performance bars
    """
    methods = df.columns[:-1]

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
    method_counts = []
    for method in methods:
        solved = df[method].sum()
        method_counts.append(solved)

    # Sort by performance
    method_data = list(zip(methods, method_counts))
    method_data.sort(key=lambda x: x[1], reverse=True)
    sorted_methods = [m for m, _ in method_data]
    sorted_counts = [c for _, c in method_data]

    method_names_short = [m.replace('grammar_', '') for m in sorted_methods]
    y_pos = np.arange(len(methods))

    # Color bars by performance
    colors_perf = ['#10b981' if c/len(df) > 0.7 else
                   '#f59e0b' if c/len(df) > 0.4 else
                   '#ef4444' for c in sorted_counts]

    ax_method.barh(y_pos, sorted_counts, color=colors_perf, alpha=0.7, edgecolor='black', linewidth=1.5)
    ax_method.set_yticks(y_pos)
    ax_method.set_yticklabels(method_names_short, fontsize=11, fontweight='bold')
    ax_method.set_xlabel('Total Benchmarks Solved', fontsize=13, fontweight='bold')
    ax_method.set_title('Individual Method Performance (sorted by performance)',
                       fontsize=12, fontweight='bold')
    ax_method.grid(axis='x', alpha=0.3, linestyle='--')
    ax_method.set_xlim(0, len(df) * 1.2)

    # Add detailed labels on bars
    for i, (count, method) in enumerate(zip(sorted_counts, sorted_methods)):
        percentage = 100 * count / len(df)
        ax_method.text(count + len(df)*0.01, i,
                      f'{count}/{len(df)} ({percentage:.1f}%)',
                      va='center', fontsize=10, fontweight='bold')

    plt.tight_layout()
    return fig, df_sorted

# Assuming your dataframe is called 'df'
# df = your_dataframe

# Create plots for each type
print("Generating plots...")
fig_all, sorted_all = create_heatmap_and_performance(df, "All Benchmarks")
print("✓ Saved: heatmap_all.png")

fig_int, sorted_int = create_heatmap_and_performance(
    df[df['type'] == 'Int'], "Int Benchmarks")
print("✓ Saved: heatmap_int.png")

fig_bool, sorted_bool = create_heatmap_and_performance(
    df[df['type'] == 'Bool'], "Bool Benchmarks")
print("✓ Saved: heatmap_bool.png")

plt.show()

# Print detailed statistics
print("\n" + "="*70)
print("BENCHMARK COVERAGE ANALYSIS")
print("="*70)

methods = df.columns[:-1]

for type_filter, type_name in [(None, "All"), ("Int", "Int"), ("Bool", "Bool")]:
    if type_filter:
        subset = df[df['type'] == type_filter]
    else:
        subset = df

    print(f"\n{'='*70}")
    print(f"{type_name} Benchmarks - Total: {len(subset)}")
    print('='*70)

    # Method performance
    print("\nMethod Performance:")
    print("-"*70)
    for method in methods:
        solved = subset[method].sum()
        print(f"{method:20s}: {solved:4d}/{len(subset):4d} ({100*solved/len(subset):5.1f}%)")

    # Coverage statistics
    subset_copy = subset.copy()
    subset_copy['n_solved'] = subset_copy[methods].sum(axis=1)

    print("\nCoverage Distribution:")
    print("-"*70)
    for n in range(7):
        count = (subset_copy['n_solved'] == n).sum()
        if count > 0:
            label = f"Solved by {n} methods" if n > 0 else "UNSOLVED"
            print(f"{label:25s}: {count:4d} ({100*count/len(subset):5.1f}%)")

    # Show unsolved benchmarks
    unsolved = subset[subset[methods].sum(axis=1) == 0]
    if len(unsolved) > 0:
        print(f"\nUnsolved Benchmarks ({len(unsolved)}):")
        print("-"*70)
        for name in unsolved.index[:10]:
            print(f"  • {name}")
        if len(unsolved) > 10:
            print(f"  ... and {len(unsolved) - 10} more")

    # Show only solved by one method
    solved_by_one = subset[subset[methods].sum(axis=1) == 1]
    if len(solved_by_one) > 0:
        print(f"\nSolved by Only ONE Method ({len(solved_by_one)}):")
        print("-"*70)
        for name in solved_by_one.index[:5]:
            which = [m for m in methods if solved_by_one.loc[name, m]]
            print(f"  • {name:40s} → {which[0].replace('grammar_', '')}")
        if len(solved_by_one) > 5:
            print(f"  ... and {len(solved_by_one) - 5} more")

print("\n" + "="*70)
