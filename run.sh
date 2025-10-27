f=examples/LIA/s1.sl
python3 python_frontend.py "$f"
cargo r --release --features heuristic-default -- "$f"
