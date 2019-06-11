#!/bin/bash
set -e 

# opensmt2
pushd .
git clone https://scm.ti-edu.ch/repogit/opensmt2.git
# git clone https://github.com/dddejan/opensmt2.git
cd opensmt2
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Release -DPRODUCE_PROOF=ON ..
make 
sudo make install
popd 