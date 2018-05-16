#!/bin/bash
set -e 

# libpoly
pushd .
git clone https://github.com/SRI-CSL/libpoly.git
cd libpoly/build
cmake -DCMAKE_BUILD_TYPE=Release ..
sudo make install
popd 

# cudd
pushd .
git clone https://github.com/ivmai/cudd.git
cd cudd
git checkout tags/cudd-3.0.0
./configure --enable-shared
sudo make install
popd

# yices2
pushd .
git clone https://github.com/SRI-CSL/yices2.git
cd yices2
git checkout mcsat-bv
autoconf
./configure --enable-mcsat 
make 
sudo make install
popd 