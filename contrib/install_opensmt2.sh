#!/bin/bash
set -e 

# opensmt2
pushd .
git clone --depth 1 --branch OpenSMT-2.0.0 --single-branch https://github.com/usi-verification-and-security/opensmt.git
cd opensmt
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Release -DUSE_READLINE=ON -DPACKAGE_TESTS=OFF ..
make 
sudo make install
popd
