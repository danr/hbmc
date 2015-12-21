ulimit -Sv 7000000
ghc --make Incremental.hs -o Incremental || exit

TIMEOUT=60
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --lazy-enums
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --top-level-bool-ops
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --always-later
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=False
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=False --lazy-enums
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=False --top-level-bool-ops
./Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=False --always-later
# ./Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --delay-all-datatypes
# ./Incremental False - benchmarks/sat $TIMEOUT ./hbmc-runner -q -u -d
# ./Incremental False - benchmarks-smten/sat $TIMEOUT ./smten-runner
# ./Incremental False - benchmarks-feat/sat $TIMEOUT _feat
# ./Incremental False unknown benchmarks-cvc4/sat $TIMEOUT cvc4-2015-10-10-x86_64-linux-opt --fmf-fun --dump-models
# ./Incremental False - benchmarks/sat $TIMEOUT hbmc -q
# ./Incremental False - benchmarks-lazysc/sat $TIMEOUT _lazysc
#
# TIMEOUT=10
# ./Incremental True - benchmarks/unsat $TIMEOUT hbmc -q -u -d
# ./Incremental True - benchmarks/unsat $TIMEOUT hbmc -q --memo=False -d
# ./Incremental True - benchmarks/unsat $TIMEOUT hbmc -q --merge=False --memo=False -d
# ./Incremental True - benchmarks/unsat $TIMEOUT hbmc -q --merge=False -d
# ./Incremental True - benchmarks/unsat $TIMEOUT hbmc -q -d
# ./Incremental True - benchmarks-smten/unsat $TIMEOUT _smten
# ./Incremental True - benchmarks-lazysc/unsat $TIMEOUT _lazysc


