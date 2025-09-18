#!/bin/bash

outfile=cvc_bench.txt
if [[ -n "$1" ]]; then
    outfile=$1
fi

all=$(find "examples/LIA" | wc -l)
function run() {
    i=0
    t=$(mktemp -d)
    for f in $(find "examples/LIA" -type f)
    do
        echo
        echo ==========
        echo "[$i/$all] $f:"
        timeout 10s cvc4 "$f"
        i=$(($i+1))
    done

    success=$(cat $outfile | grep unsat | wc -l)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee $outfile
