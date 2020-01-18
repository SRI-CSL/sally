#!/bin/bash
set -e 

# libpoly
pushd .
git clone https://github.com/SRI-CSL/libpoly.git
mkdir -p libpoly/build
cd libpoly/build
cmake -DCMAKE_BUILD_TYPE=Release ..
make
sudo make install
popd 

# CUDD
pushd .
git clone https://github.com/ivmai/cudd.git
cd cudd
git checkout tags/cudd-3.0.0
autoreconf -fi
./configure --enable-shared
make
sudo make install
popd


# yices2
pushd .
git clone https://github.com/SRI-CSL/yices2.git
cd yices2
autoconf
./configure --enable-mcsat 
make 
sudo make install
popd 
