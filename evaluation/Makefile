files = $(wildcard benchmarks/sat/*smt2)

lazy_hs = $(subst benchmarks,benchmarks-lazysc,$(files:.smt2=.hs))
feat_hs = $(subst benchmarks,benchmarks-feat,$(files:.smt2=.hs))
smten_hs = $(subst benchmarks,benchmarks-smten,$(files:.smt2=.hs))

all_hs = $(lazy_hs) $(feat_hs) $(smten_hs)

files_cvc4 = $(subst benchmarks,benchmarks-cvc4,$(files))

targets = $(all_hs:.hs=.bin) $(files_cvc4)

benchmarks-lazysc/%.bin: benchmarks-lazysc/%.hs
	ghc --make $< -o $@

benchmarks-feat/%.bin: benchmarks-feat/%.hs
	ghc --make $< -o $@

benchmarks-smten/%.bin: benchmarks-smten/%.hs
	smten --make $< -o $@

benchmarks-cvc4/%: benchmarks/%
	mkdir -p $$(dirname $@)
	tip $< --monomorphise --lambda-lift --axiomatize-lambdas --monomorphise --remove-match --simplify-gently --skolemise-conjecture --negate-conjecture > $@

benchmarks-lazysc/unsat/%.hs: benchmarks/unsat/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-lazysc-depth > $@

benchmarks-lazysc/sat/%.hs: benchmarks/sat/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-lazysc > $@

benchmarks-feat/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-feat > $@

benchmarks-smten/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-smten > $@

all: $(targets)

.SECONDARY: $(hs)

clean:
	rm -rf benchmarks-{cvc4,feat,lazysc,smten}/*

info:
	echo $(files)
	echo $(all_hs)
	echo $(targets)

.PHONY: all clean dirs info
