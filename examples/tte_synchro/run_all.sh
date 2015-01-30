#!/bin/bash
for file in *.*.mcmt; 
do 
  echo $file; 
  /usr/bin/time -f "%U" ../../build/src/sally --lsal-extensions $@ tte_synchro.mcmt $file; 
done;
