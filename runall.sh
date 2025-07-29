#!/bin/bash

cargo b --release

for f in $(find "examples/LIA" -type f)
do
    echo "$f:"
    timeout 10s target/release/liasynth "$f"
done
