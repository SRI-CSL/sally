#!/bin/bash
for file in *.*.mcmt; 
do 
  echo $file; 
  ../../build/src/sally --lsal-extensions $@ tte_synchro.mcmt $file; 
done;
