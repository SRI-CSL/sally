echo "RUN on `date`"

echo -e '\n\n  fixed_fault_mon_a_fail'
time sal-inf-bmc wbs_simple_7_17.sal fixed_fault_mon_a_fail -d 1 -i  
echo -e '\n\n  clock_invariant'
time sal-inf-bmc wbs_simple_7_17.sal clock_invariant -d 1 -i  

echo -e '\n\n  auto_mode_invariant'
time sal-inf-bmc wbs_simple_7_17.sal auto_mode_invariant -d 1 -i

echo -e '\n\n  redge -quicker '
time sal-inf-bmc wbs_simple_7_17.sal seen_rising_edge -d 15 -i  -l clock_invariant  

echo -e '\n\n  button_invariant'
time sal-inf-bmc wbs_simple_7_17.sal button_invariant -i  -d 3 -l seen_rising_edge  -l clock_invariant 

echo -e '\n\n  button_phase_invariant'
time sal-inf-bmc wbs_simple_7_17.sal button_phase_invariant  -i -d  14  -l seen_rising_edge  -l button_invariant  -i  -l clock_invariant  -l auto_mode_invariant
 
echo -e '\n\n  cs'
time sal-inf-bmc wbs_simple_7_17.sal cs  -i -d  15 -l seen_rising_edge  -l button_invariant  -i  -l clock_invariant  -l auto_mode_invariant  -l fixed_fault_mon_a_fail 
echo -e '\n\n  cs_b'
time sal-inf-bmc wbs_simple_7_17.sal cs_b  -i -d  15 -l seen_rising_edge  -l button_invariant  -i  -l clock_invariant  -l auto_mode_invariant  -l fixed_fault_mon_a_fail 

 
echo -e '\n\n  disagree_b'
time sal-inf-bmc wbs_simple_7_17.sal disagree_b -d 15 -i -l seen_rising_edge    -l cs_b -l clock_invariant -i  -l button_invariant -l fixed_fault_mon_a_fail -l button_phase_invariant

echo -e '\n\n  channel_b_in_control'
time sal-inf-bmc wbs_simple_7_17.sal channel_b_in_control -d 14 -i -l seen_rising_edge    -l cs_b -l clock_invariant -i  -l button_invariant -l fixed_fault_mon_a_fail -l button_phase_invariant

echo -e '\n\n  channel_a_or_b_in_control_i'
time sal-inf-bmc wbs_simple_7_17.sal channel_a_or_b_in_control -d 15 -i -l fixed_fault_mon_a_fail -l  button_phase_invariant -l seen_rising_edge    -l cs_b -l clock_invariant -i  -l button_invariant -l button_phase_invariant
