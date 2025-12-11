#!/bin/bash

for x in $(cd examples/LIA; ls MPwL_*)
do
    python handle_mpwl.py examples/LIA/$x > t/$x
done
