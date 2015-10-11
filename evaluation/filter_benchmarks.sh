#!/bin/bash

# get rid of icky apostrophes
rename \' 2 benchmarks/**/*.smt2 -v
for i in benchmarks/**/*.smt2; do
  # try to make everything datatypes
  tip --int-to-nat --type-skolem-conjecture --sorts-to-nat $i > /tmp/a && cp /tmp/a $i

  # remove problems with arithmetic and higher order functions
  (grep '[() ]@[() ]' $i || grep '[() ]Int[() ]' $i) && rm $i -v
done
