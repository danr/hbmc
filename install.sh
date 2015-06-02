#!/bin/bash
cabal install bnfc
git clone https://github.com/tip-org/tools
(cd tools; git checkout 76734bd886a571edb0b2a1bc355d50228be70246; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
