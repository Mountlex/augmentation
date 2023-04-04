cargo run --release -- path 2 7 c3 -o proofs  -n 3 -e 1 
cargo run --release -- path 2 7 c4 -o proofs  -n 3 -e 5 
cargo run --release -- path 2 7 c5 -o proofs  -n 2 -e 3 
cargo run --release -- path 2 7 c6 -o proofs  -n 1 -e 3 
cargo run --release -- path 2 7 l -o proofs  -n 2 -e 5 
cargo run --release -- path 2 7 cp -o proofs  -n 3 -e 1
cargo run --release -- path 2 7 ct -o proofs  -n 3 -e 1

# ohne 4-matching: 116s (incl build)