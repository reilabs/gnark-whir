## How to run

1. `git clone https://github.com/reilabs/ProveKit`
2. `cd ProveKit && git checkout add-prover`
3. Example: `cargo +beta run --bin prover`
 This will generate params and proof files
4. `cd .. && git clone https://github.com/reilabs/gnark-whir`
5. `cd gnark-whir`
6. `go run .`

