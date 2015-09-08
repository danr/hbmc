#!/bin/bash

cat $1 | sed 's/.*,//' | grep -v - | ghc -e "interact (unlines . map (show . logBase 10 . read) . lines)"
