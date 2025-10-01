f=examples/LIA/array_search_10.sl
python3 python_frontend.py "$f"
RUSTFLAGS="-C force-frame-pointers=yes" cargo flamegraph -- "$f"
