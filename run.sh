f=examples/LIA/$1.sl
python3 python_frontend.py "$f"
cargo r --release -- "$f"
