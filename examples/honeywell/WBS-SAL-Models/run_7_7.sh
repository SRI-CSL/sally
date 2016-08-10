echo "RUN on `date`"

echo -e '\n\n  clock_invariant'
time sal-inf-bmc wbs_simple_7_7.sal clock_invariant -d 1 -i  

echo -e '\n\n  auto_mode_invariant'
time sal-inf-bmc wbs_simple_7_7.sal auto_mode_invariant -d 1 -i

echo -e '\n\n  redge -quicker '
time sal-inf-bmc wbs_simple_7_7.sal seen_rising_edge -d 15 -i  -l clock_invariant  

echo -e '\n\n  button_invariant'
time sal-inf-bmc wbs_simple_7_7.sal button_invariant -i  -d 3 -l seen_rising_edge  -l clock_invariant 
 
echo -e '\n\n  cs'
time sal-inf-bmc wbs_simple_7_7.sal cs  -i -d  11 -l seen_rising_edge  -l button_invariant  -i  -l clock_invariant  -l auto_mode_invariant
 
echo -e '\n\n  disagree_a'
time sal-inf-bmc wbs_simple_7_7.sal disagree_a -d 14 -i -l seen_rising_edge    -l cs -l clock_invariant -i  -l button_invariant

echo -e '\n\n  disagree_b'
time sal-inf-bmc wbs_simple_7_7.sal disagree_b -d 14 -i -l seen_rising_edge    -l cs -l clock_invariant -i  -l button_invariant

echo -e '\n\n  channel_a_in_control'
time sal-inf-bmc wbs_simple_7_7.sal channel_a_in_control -d 14 -i -l seen_rising_edge    -l cs -l clock_invariant -i  -l button_invariant
