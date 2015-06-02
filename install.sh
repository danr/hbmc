#!/bin/bash
cabal install bnfc
git clone https://github.com/tip-org/tools
(cd tools; git checkout de6959b81fc7dcc80d19df04a04f8d6f1511fb45; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
