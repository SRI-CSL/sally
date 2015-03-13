#!/bin/bash
FILE=$1

cat $1 |
  grep -v set-option |
  sed s/'|'/''/g |
  sed s/'::'/'_'/g |
  sed s/'(push 1)'/'(push)'/g |
  sed s/'(pop 1)'/'(pop)'/g | 
  sed s/'(check-sat)'/'(check)'/g |
  sed s/' () Real'/'::real'/g | 
  sed s/' () Bool'/'::bool'/g |
  sed s/'declare-fun'/'define'/ |
  perl -p0e s/'\(get-value\s*\([^\)]*\)\s*\)'/'\(show-model\)'/smg
  
