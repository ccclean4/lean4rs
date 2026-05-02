set -x
rm lean4
rustc lean4.rs
RUST_BACKTRACE=1 ./lean4
