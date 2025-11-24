#!/bin/bash

mkdir t

for x in $(cd examples/LIA; ls MPwoL_*)
do
    ./denest.py examples/LIA/$x > t/$x
done
