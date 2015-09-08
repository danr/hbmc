#!/bin/bash

prep() {
    cat $1 | grep -v msorttd | grep -v ssort | sed 's/.*,//' | sed 's/-/60/'
}

echo x y
pr -m -t <(prep $1) <(prep $2) | sed 's/\s\+/ /'

