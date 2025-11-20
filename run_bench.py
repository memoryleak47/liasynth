import subprocess
import itertools
import sys
import os


try: 
    _, indir, outdir = sys.argv
except:
    raise Exception("missing arguments")

os.makedirs(outdir, exist_ok=True)

g1 = [None, "learned-heuristic"]
g2 = [None, "simple", "winning"]
g3 = [None, "total"]

heur_tag = lambda v: "l" if v == "learned-heuristic" else "d"
inc_tag = lambda v: "_w" if v == "winning" else "_s" if v == "simple" else ""
tot_tag = lambda x: "t" if x == "total" else ""

for o1, o2, o3 in itertools.product(g1, g2, g3):
    opts = [v for v in (o1, o2, o3) if v is not None]
    opts_str = ", ".join(opts)

    if o2 is None:
        if o3 is not None:
            continue

    outfile = f"{outdir}/grammar_{heur_tag(o1)}{inc_tag(o2)}{tot_tag(o3)}.txt"

    cmd = ["./runall_dir.sh"]
    cmd.append(f"{opts_str}")
    cmd.append(indir)
    cmd.append(outfile)

    print("Running:", " ".join(f'"{c}"' if " " in c else c for c in cmd))
    subprocess.run(cmd, check=True)
