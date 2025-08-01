#!/bin/bash

cargo b --release

function run() {
    for f in $(find "examples/LIA" -type f)
    do
        echo
        echo ==========
        echo "$f:"
        timeout 10s target/release/liasynth "$f"
    done

    success=$(cat bench.txt | grep Answer | wc -l)
    all=$(find "examples/LIA" | wc -l)

    echo
    echo "Completed $success/$all"
}

run 2>&1 | tee bench.txt
