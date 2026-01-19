f=examples/LIA/max4.sl
python3 python_frontend.py "$f"
RUSTFLAGS="-C force-frame-pointers=yes" cargo flamegraph --features "default, winning" -- "$f"
firefox flamegraph.svg
