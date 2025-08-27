.PHONY: bench perform

export NAME=Others
export SUBNAME=bin_prot-2

SHELL=/usr/bin/env bash -o pipefail

bench:
	@date -u +"%FT%TZ - $(NAME)/$(SUBNAME): starting"
	mkdir -p ../../../../janestreet/bench/bin_prot-2/
	cp -f dune bench_lists.ml bench_numbers.ml bin_prot_bench.ml bench.ml \
    ../../../../janestreet/bench/bin_prot-2/
	cd ../../../../janestreet/bench/bin_prot-2 && dune build --root ../.. --profile release --verbose bench/bin_prot-2/bench.bc.js #bench/bin_prot-2/bench.bc.wasm.js
	cp -rf ../../../../janestreet/_build/default/bench/bin_prot-2/bench.bc* .
	#$(MAKE) perform COMPILER=js_of_ocaml SCRIPT=bench.bc.js KIND=js
	#$(MAKE) perform COMPILER=wasm_of_ocaml SCRIPT=bench.bc.wasm.js KIND=wasm
	@date -u +"%FT%TZ - $(NAME)/$(SUBNAME): done"

perform:
	env time -f '{"compiler": "$(COMPILER)", "time":"%E"}' node $(SCRIPT) 2>&1 1> /dev/null | \
	tee /dev/stderr | \
	sh ../../utils/format_metrics.sh exec | \
	sh ../../utils/aggregate.sh $(KIND)
