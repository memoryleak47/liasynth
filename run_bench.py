import subprocess
import itertools
import sys
import os
import shutil
from concurrent.futures import ThreadPoolExecutor, as_completed

try:
    _, indir, outdir = sys.argv
except:
    raise Exception("missing arguments")

base_dir = os.getcwd()
outdir = os.path.abspath(outdir)
os.makedirs(outdir, exist_ok=True)

g1 = ["expert, lia", "expert, rf", "size", "random", "learned"]
g2 = [None, "winning"]
g3 = [None, "total"]

heur_tag = lambda v: "l" if v == "learned" else "r" if v == "random" else "s" if v == "size" else "el" if 'lia' in v else 'er'
inc_tag = lambda v: "_w" if v == "winning" else "_s" if v == "simple" else ""
tot_tag = lambda x: "t" if x == "total" else ""

jobs = []
run_idx = 1

for o1, o2, o3 in itertools.product(g1, g2, g3):
    if o2 is None and o3 is not None:
        continue

    opts = [v for v in (o1, o2, o3) if v is not None]
    opts_str = ", ".join(opts)

    outfile = os.path.join(
        outdir,
        f"grammar_{heur_tag(o1)}{inc_tag(o2)}{tot_tag(o3)}.txt"
    )
    outfile_abs = os.path.abspath(outfile)

    rundir = os.path.join(base_dir, f"rundir_{run_idx}")
    run_idx += 1

    if os.path.exists(rundir):
        shutil.rmtree(rundir)

    shutil.copytree(
        base_dir,
        rundir,
        ignore=shutil.ignore_patterns("rundir_*")
    )

    cmd = ["./runall_dir.sh", opts_str, indir, outfile_abs]

    printable_cmd = " ".join(f'"{c}"' if " " in c else c for c in cmd)
    print(f"Running in {rundir}: {printable_cmd}")

    jobs.append((cmd, rundir))

max_workers = 2

with ThreadPoolExecutor(max_workers=max_workers) as ex:
    futures = {
        ex.submit(subprocess.run, cmd, check=True, cwd=rundir): (cmd, rundir)
        for cmd, rundir in jobs
    }
    for fut in as_completed(futures):
        cmd, rundir = futures[fut]
        try:
            fut.result()
        except Exception as e:
            print("Command failed:", cmd, "in", rundir, "error:", e)

