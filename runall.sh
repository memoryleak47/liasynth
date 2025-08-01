#!/bin/bash

cargo b --release
outfile=bench.txt
if [[ -n "$1" ]]; then
    outfile=$1
fi

function run() {
    t=$(mktemp -d)
    cp target/release/liasynth $t
    for f in $(find "examples/LIA" -type f)
    do
        echo
        echo ==========
        echo "$f:"
        timeout 10s $t/liasynth "$f"
    done

    success=$(cat $outfile | grep Answer | wc -l)
    all=$(find "examples/LIA" | wc -l)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee $outfile
