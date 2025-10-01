import re
import os
import sys
import signal
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed

from more_itertools import bucket
from collections import defaultdict

import pandas as pd


cvc5sol_pat = re.compile(r'(Int|Bool)\s(.*)\)')
lias_pat     = re.compile(r'Answer:\s*(.*)')

def run_shell(cmd, timeout, env=None, cwd=None):
    p = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        shell=True,
        cwd=cwd,
        env=env,
        start_new_session=True,
        close_fds=True,
    )
    try:
        out, _ = p.communicate(timeout=timeout)
        return out or ""
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.wait()
        return "timeout"
    except Exception:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.wait()
        return "fail"

def run_lia_cvc5(benchmark, results, incr_type, timeout=10):
    lia_path  = f"examples/LIA/{benchmark}"
    clen_path = f"examples/cleaned-LIA/{benchmark}"

    cmds = {
        f"liasynth_{incr_type}":       f'python python_frontend.py {lia_path} && RUSTFLAGS="-Awarnings" cargo run --release --features {incr_type} -- {lia_path}',
        # "cvc5":           f'cvc5 --lang=sygus2 {lia_path}',
        # "liasynth_clean": f'python python_frontend.py {clen_path} && RUSTFLAGS="-Awarnings" cargo run -j4 --release -- {clen_path}',
        # "cvc5_clean":     f'cvc5 --lang=sygus2 {clen_path}',
    }

    with ThreadPoolExecutor(max_workers=2) as ex:
        futs = {
            ex.submit(run_shell, cmd, timeout, os.environ.copy(), None): name
            for name, cmd in cmds.items()
        }

        for fut in as_completed(futs):
            name = futs[fut]
            out = fut.result()

            results[name]['benchmark'].append(benchmark)

            if name.startswith("cvc5"):
                m = cvc5sol_pat.search(out)
                if m:
                    results[name]['status'].append('success')
                    results[name]['solution'].append(m.group(2))
                    continue
            else:
                m = lias_pat.search(out)
                if m:
                    results[name]['status'].append('success')
                    results[name]['solution'].append(m.group(1))
                    continue

            if 'infeasible' in out:
                results[name]['status'].append('infeasible')
            else:
                results[name]['status'].append(out)
            results[name]['solution'].append('-')

def run_all(folder, *, incr_type, timeout):
    results = defaultdict(lambda: defaultdict(list))
    l = len(os.listdir(folder))
    for i, fname in enumerate(os.listdir(folder), start=1):
        run_lia_cvc5(fname, results, incr_type, timeout)
        print(
            f"[{i}/{l}]",
            fname,
            # f"\n\tcvc5: {results['cvc5']['status'][-1]}",
            # f"\n\tcvc5_clean: {results['cvc5_clean']['status'][-1]}",
            f"\n\tlia_{incr_type}: {results[f'liasynth_{incr_type}']['status'][-1]}",
            # f"\n\tlia_clean: {results['liasynth_clean']['status'][-1]}",
        )

    # pd.DataFrame.from_dict(results['cvc5']).to_csv('cvc5_LIA_res.csv', index=False)
    # pd.DataFrame.from_dict(results['cvc5_clean']).to_csv('results/cvc5_cLIA_res.csv', index=False)
    pd.DataFrame.from_dict(results[f'liasynth_{incr_type}']).to_csv(f'results/lia_{incr_type}.csv', index=False)
    # pd.DataFrame.from_dict(results['liasynth_clean']).to_csv('results/lia_cLIA_res.csv', index=False)

incr_type = 'default'
if len(sys.argv) == 2:
    incr_type = sys.argv[1]

run_all('examples/LIA', incr_type=incr_type, timeout=10)
