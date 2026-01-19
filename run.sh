python python_frontend.py "$1"
 RUSTFLAGS="-Awarnings" cargo run --release --features default "$1"
