#!/bin/bash
ghc --make Incremental.hs
cp ~/bin/cvc4-* remote/bin
cp ~/.cabal/bin/hbmc-symbo remote/bin
cp ~/.cabal/bin/hbmc-normal remote/bin
cp hbmc-runner remote/bin
cp smten-runner remote/bin
cp Incremental remote/bin
cp benchmarks* remote -r
cp qbench.sh remote
