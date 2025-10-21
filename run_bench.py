import subprocess
import itertools

# Option groups
g1 = [None, "ignore-grammar"]
g2 = ["heuristic-default", "heuristic-linr"]
g3 = [None, "winning-incremental", "winning-incremental, total-incremental"]

def grammar_tag(v):
    return "ignor-grammar" if v == "ignore_" else ""

def heur_tag(v):
    return "d" if v == "heuristic-default" else "l"

def inc_tag(v):
    if v is None:
        return ""
    if v == "winning-incremental":
        return "_w"
    return "_wt"  

for o1, o2, o3 in itertools.product(g1, g2, g3):
    opts = [v for v in (o1, o2, o3) if v is not None]
    opts_str = ", ".join(opts)

    outfile = f"benchmarking2/{grammar_tag(o1)}grammar_{heur_tag(o2)}{inc_tag(o3)}.txt"

    cmd = ["./runall.sh"]
    cmd.append(f"{opts_str}")
    cmd.append(outfile)

    print("Running:", " ".join(f'"{c}"' if " " in c else c for c in cmd))
    subprocess.run(cmd, check=True)
