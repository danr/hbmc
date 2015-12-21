remove = $(foreach v,$(2),$(if $(findstring $(1),$(v)),,$(v)))

files = $(wildcard benchmarks/sat/*smt2)

lazy_hs = $(subst benchmarks,benchmarks-lazysc,$(files:.smt2=.hs))
lazy_simple_hs = $(subst benchmarks,benchmarks-lazysc-simple,$(files:.smt2=.hs))
feat_hs = $(subst benchmarks,benchmarks-feat,$(files:.smt2=.hs))
smten_hs = \
  $(call remove,scale_, \
  $(call remove,sudoku_, \
  $(call remove,prop_, \
  $(call remove,typeboth_, \
  $(call remove,parse_,    \
  $(subst benchmarks,benchmarks-smten,$(files:.smt2=.hs)))))))

easy_hs = $(lazy_hs) $(lazy_simple_hs) $(feat_hs) $(smten_hs)

files_cvc4 = $(subst benchmarks,benchmarks-cvc4,$(files))

targets = $(easy_hs:.hs=.bin) $(files_cvc4)
smten_targets = $(smten_hs:.hs=.bin)

benchmarks-lazysc/%.bin: benchmarks-lazysc/%.hs
	ghc --make $< -o $@

benchmarks-lazysc-simple/%.bin: benchmarks-lazysc-simple/%.hs
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

benchmarks-lazysc-simple/sat/%.hs: benchmarks/sat/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-lazysc-simple > $@

benchmarks-feat/%.hs: benchmarks/%.smt2
	mkdir -p $$(dirname "$@")
	tip $< --haskell-feat > $@

benchmarks-smten/%.hs: benchmarks/%.smt2
	rm Smten -rf
	mkdir -p $$(dirname "$@")
	tip $< --haskell-smten > $@

all: $(targets)
smten: $(smten_targets)

.SECONDARY: $(hs)

clean:
	rm -rf benchmarks-{cvc4,feat,lazysc,smten}/*

info:
	echo $(files)
	echo $(all_hs)
	echo $(targets)
	echo $(smten_targets)

.PHONY: all clean dirs info
