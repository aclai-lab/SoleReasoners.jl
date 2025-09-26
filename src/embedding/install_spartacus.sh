#!/bin/bash
# This script installs spartacus in a subfolder
cd $1
curl https://www.ps.uni-saarland.de/spartacus/spartacus-1.1.3.tar.bz2 -o spartacus-1.1.2.tar.bz2
tar -x -f spartacus-1.1.2.tar.bz2
cd spartacus
make spartacus