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
        echo
        echo ==========
        echo "[$i/$all] $f:"

	start_ts=$(date +%s%3N)

        timeout 120s cvc5 "$f" --force-logic=NIA

	end_ts=$(date +%s%3N)
	echo "Time: $((end_ts - start_ts))ms"
        i=$(($i+1))
    done

    success=$(cat $outfile | grep define-fun | wc -l)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee $outfile
