## How to run

1. `git clone https://github.com/reilabs/whir`
2. `cd whir && git checkout skyscraper`
3. Example: `cargo +nightly run --release -- -d=24  --fold=4 --field=Field256`
 This will generate params and proof files
4. `cd .. && git clone https://github.com/reilabs/gnark-whir`
5. `cd gnark-whir`
6. `go run .`
(optional, for minimum number of constraints) 7. In gnark-whir/go.mod, add `replace github.com/consensys/gnark => /local_path_to_gnark` to line 4
