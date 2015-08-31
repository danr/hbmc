#!/bin/bash
cabal install bnfc
git clone https://github.com/tip-org/tools
(cd tools; git checkout fa9767158ba93e0c5f0717a6a9ef93741e24d27; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
