#!/bin/bash
cp ~/code/tip-benchmarks/benchmarks . -r
(cd benchmarks; ls -I sat | xargs rm -rf)
./filter_benchmarks.sh                    # shouldn't do anything
make -j4
make smten
