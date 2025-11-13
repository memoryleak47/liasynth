import subprocess
import itertools
import sys


try: 
    _, indir, outdir = sys.argv
except:
    raise Exception("missing arguments")


g2 = ["heuristic-default", "heuristic-linr"]
g3 = [None, "winning-incremental", "winning-incremental, total-incremental"]

def heur_tag(v):
    return "d" if v == "heuristic-default" else "l"

def inc_tag(v):
    if v is None:
        return ""
    if v == "winning-incremental":
        return "_w"
    return "_wt"  

for o2, o3 in itertools.product(g2, g3):
    opts = [v for v in (o2, o3) if v is not None]
    opts_str = ", ".join(opts)

    outfile = f"{outdir}/grammar_{heur_tag(o2)}{inc_tag(o3)}.txt"

    cmd = ["./runall_dir.sh"]
    cmd.append(f"{opts_str}")
    cmd.append(indir)
    cmd.append(outfile)

    print("Running:", " ".join(f'"{c}"' if " " in c else c for c in cmd))
    subprocess.run(cmd, check=True)
