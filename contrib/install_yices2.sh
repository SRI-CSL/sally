#!/bin/bash
set -e

# Find Homebrew prefix for macOS and set build flags for dependencies
if [[ "$(uname)" == "Darwin" ]]; then
  if [ -d /opt/homebrew ]; then
    BREW_PREFIX=/opt/homebrew
  else
    BREW_PREFIX=/usr/local
  fi
  export CPPFLAGS="-I$BREW_PREFIX/include"
  export LDFLAGS="-L$BREW_PREFIX/lib"
  export PKG_CONFIG_PATH="$BREW_PREFIX/lib/pkgconfig"
  export LD_LIBRARY_PATH="$BREW_PREFIX/lib:$LD_LIBRARY_PATH"
  echo "[INFO] macOS build flags set:"
  echo "CPPFLAGS=$CPPFLAGS"
  echo "LDFLAGS=$LDFLAGS"
  echo "PKG_CONFIG_PATH=$PKG_CONFIG_PATH"
  echo "LD_LIBRARY_PATH=$LD_LIBRARY_PATH"
fi

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
export LD_LIBRARY_PATH=/usr/local/lib/:${LD_LIBRARY_PATH}
autoconf
./configure --enable-mcsat
make
sudo make install
popd
