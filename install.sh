#!/bin/bash
git clone https://github.com/augustss/geniplate.git
(cd geniplate; cabal install)
git clone https://github.com/tip-org/tools
(cd tools; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
