#!/bin/bash
cabal install bnfc
git clone https://github.com/augustss/geniplate.git
(cd geniplate; cabal install . 'mtl < 2.2')
git clone https://github.com/tip-org/tools
(cd tools; git checkout ec8665aeab0706dda20c33f177d86cf0290c23c8; ./make_parser.sh; cabal install tip-lib/ tip-haskell-frontend/)
cabal install
