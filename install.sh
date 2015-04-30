#!/bin/bash
cabal install bnfc
git clone https://github.com/tip-org/tools
(cd tools; git checkout 3ae13246fefbab207601c33fefb39ead47dcc6c1; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
