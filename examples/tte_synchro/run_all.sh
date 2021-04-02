#!/bin/bash
for file in *.*.mcmt; 
do 
  echo $file; 
  sally -v 1 --engine pdkind --lsal-extensions $@ tte_synchro.mcmt $file; 
done;
