#!/bin/bash

if [ $# -ne 2 ]; then
    echo "Usage: $0  <directory> <outfile>"
    exit 1
fi

indir="$1"
outfile="$2"

all=$(find "$indir" -type f -name "*.sl" | wc -l)
function run() {
    i=0
    t=$(mktemp -d)
    for f in $(find "$indir" -type f -name "*.sl" | sort); do
    do
        echo
        echo ==========
        echo "[$i/$all] $f:"
        timeout 120s cvc5 --sygus-rewrite=none "$f"
        i=$(($i+1))
    done

    success=$(cat $outfile | grep unsat | wc -l)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee $outfile
