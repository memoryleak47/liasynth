#!/usr/bin/env bash

outfile="${1:-bench.txt}"

all=$(find "examples/LIA" -type f | wc -l)

run() {
    i=0
    for f in $(find "examples/LIA" -type f | sort); do
        echo
        echo "=========="
        echo "[$i/$all] $f:"

        python3 python_frontend.py "$f"
        if ! cargo b --release >/dev/null 2>&1; then
            echo "[build failed] $f"
            i=$((i+1))
            continue
        fi
        timeout 10s target/release/liasynth "$f"

        i=$((i+1))
    done

    success=$(grep -c "Answer" "$outfile" || true)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee "$outfile"
