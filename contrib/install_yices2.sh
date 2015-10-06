#!/bin/bash
set -e 

# Check if the yices2 folder is empty
if [ ! -d "$HOME/yices2/lib" ]; then
  wget "http://yices.csl.sri.com/cgi-bin/yices2-newnewdownload.cgi?file=yices-2.3.1-src.tar.gz&accept=I+Agree" -O yices.tar.gz
  tar xzvf yices.tar.gz
  cd yices* && autoconf && ./configure --prefix=$HOME/yices2 && make MODE=release && make MODE=release install && cd ..
else
  echo 'Using cached directory.';
fi
