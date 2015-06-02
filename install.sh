#!/bin/bash
cabal install bnfc
git clone https://github.com/tip-org/tools
(cd tools; git checkout 1cea573b6765ce528b1266794cef4c33e3012c97; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
