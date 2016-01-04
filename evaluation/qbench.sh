#!/bin/bash
TIMEOUT=60
mkdir -p results
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno --merge=no
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno --lazy-enums
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno --top-level-bool-ops
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno --always-later
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --dyno --age

#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --merge=no
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --lazy-enums
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --top-level-bool-ops
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --always-later
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --age
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no --merge=no
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no --lazy-enums
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no --top-level-bool-ops
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no --always-later
#qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-symbo -q --memo=no --age

# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --delay-all-datatypes
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q -c
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --merge=no
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --memo=no
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --memo=no --delay-all-datatypes
qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --memo=no -c
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-normal -q --memo=no --merge=no
#
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-runner -q -d
# qsub -cwd -b y Incremental False - benchmarks/sat $TIMEOUT hbmc-runner -q -u -d
#
# qsub -cwd -b y Incremental False - benchmarks-smten/sat $TIMEOUT smten-runner
#
# qsub -cwd -b y Incremental False - benchmarks-feat/sat $TIMEOUT _feat
#
# qsub -cwd -b y Incremental False unknown-not_supported benchmarks-cvc4/sat $TIMEOUT cvc4-2015-12-19-x86_64-linux-opt --fmf-fun --dump-models
#
# qsub -cwd -b y Incremental False - benchmarks-lazysc/sat $TIMEOUT _lazysc
# qsub -cwd -b y Incremental False - benchmarks-lazysc-simple/sat $TIMEOUT _lazysc-simple

qstat -u \*
