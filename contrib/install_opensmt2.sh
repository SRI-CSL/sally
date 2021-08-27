#!/bin/bash
set -e 

# opensmt2
pushd .
git clone --depth 1 --branch v2.1.0 --single-branch https://github.com/usi-verification-and-security/opensmt.git
cd opensmt
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_EXECUTABLES=OFF -DPACKAGE_TESTS=OFF ..
make 
sudo make install
popd
