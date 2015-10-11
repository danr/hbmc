files = $(wildcard benchmarks/**/*smt2)

lazy_hs = $(subst benchmarks,benchmarks-lazysc,$(files:.smt2=.hs))
feat_hs = $(subst benchmarks,benchmarks-feat,$(files:.smt2=.hs))
smten_hs = $(subst benchmarks,benchmarks-smten,$(files:.smt2=.hs))

all_hs = $(lazy_hs) # $(smten_hs) # $(feat_hs)

# files_cvc4 = $(wildcard benchmarks-cvc4/*smt2)
# sk_targets = $(subst cvc4,sk,$(files_cvc4))

targets = $(all_hs:.hs=.bin)

benchmarks-lazysc/%.bin: benchmarks-lazysc/%.hs
	ghc --make $< -o $@

benchmarks-smten/%.bin: benchmarks-smten/%.hs
	smten --make $< -o $@

# benchmarks-sk/%: benchmarks-cvc4/%
# 	mkdir -p $$(dirname $@)
# 	tip $< --make-conjecture 0 --skolemise-conjecture --negate-conjecture > $@

benchmarks-lazysc/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-lazysc-depth > $@

benchmarks-smten/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip --bool-op-to-if --remove-builtin-bool --haskell-smten $< > $@

benchmarks-feat/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-feat > $@

all: $(targets)

.SECONDARY: $(hs)

clean:
	rm -rf benchmarks-sk/*
	rm -rf benchmarks-feat/*
	rm -rf benchmarks-lazysc/*
	rm -rf benchmarks-smten/*

info:
	echo $(files)
	echo $(all_hs)
	echo $(targets)

.PHONY: all clean dirs info
