#!/usr/bin/env bash
if [ $# -ne 3 ]; then
    echo "Usage: $0 <feature> <directory> <outfile>"
    exit 1
fi
feature="$1"
indir="$2"
outfile="$3"
all=$(find "$indir" -type f -name "*.sl" | wc -l)
run() {
    i=0
    for f in $(find "$indir" -type f -name "*.sl" | sort); do
        echo
        echo "=========="
        echo "[$i/$all] $f:"

	start_ts=$(date +%s%3N)

        python3 python_frontend.py "$f"
        if ! cargo b --release --features "$feature" >/dev/null 2>&1; then
            echo "[build failed] $f"
            i=$((i+1))
            continue
        fi
	prlimit --as=21474836480 timeout 120s target/release/liasynth "$f"

	end_ts=$(date +%s%3N)
	echo "Time: $((end_ts - start_ts))ms"
        i=$((i+1))
    done
    success=$(grep -c "Answer" "$outfile" || true)
    echo
    echo "Completed $success/$all"
}
run 2>&1 | tee "$outfile"
