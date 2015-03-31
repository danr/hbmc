#!/bin/bash
git clone https://github.com/augustss/geniplate.git
(cd geniplate; cabal install)
git clone https://github.com/tip-org/tools
(cd tools; git checkout ef4241f7b9703d09c2fd12bee22eef46bdaf2d1a; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
