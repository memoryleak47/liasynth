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
}

run 2>&1 | tee bench.txt
