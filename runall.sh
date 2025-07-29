#!/bin/bash

for f in $(ls examples/LIA)
do
    timeout 30s cargo r --release "examples/LIA/$f"
done
