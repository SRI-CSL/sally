#!/bin/sh
#
# proof script for mvs_with_timeouts4.sal
#
# This assumes that sal-inf-bmc is in your path and mvs_with_timeouts4.sal
# is in the current directory.
# 

verbosity=0

echo "proving time_positive"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4.sal time_positive
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4.sal time_positive

echo "proving fcm_timeout_bounds1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4.sal fcm_timeout_bounds1
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4.sal fcm_timeout_bounds1

echo "proving fcm_timeout_bounds3"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 fcm_timeout_bounds3
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 fcm_timeout_bounds3

echo "proving mvs_timeout_bounds1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 mvs_timeout_bounds1
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 mvs_timeout_bounds1

echo "proving mvs_timeout_bounds2"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 mvs_timeout_bounds2
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 mvs_timeout_bounds2

echo "proving y_init1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_init1 -l time_positive
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_init1 -l time_positive

echo "proving y_init3"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_init3 -l time_positive
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_init3 -l time_positive

echo "proving pre_y_init1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_init1  -l y_init1
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_init1  -l y_init1

echo "proving pre_y_init3"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_init3  -l y_init3
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_init3  -l y_init3


echo "proving y_invar1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_invar1 -l y_init1
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_invar1 -l y_init1

echo "proving y_invar3"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_invar3 -l y_init3
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 y_invar3 -l y_init3



echo "proving pre_y_invar1"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_invar1  -l y_invar1
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_invar1  -l y_invar1

echo "proving pre_y_invar3"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_invar3  -l y_invar3
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 pre_y_invar3  -l y_invar3


echo "proving mvs_bounds1"
echo sal-inf-bmc -i -d 2 -v $verbosity mvs_with_timeouts4 mvs_bounds1  -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 -l mvs_timeout_bounds1
sal-inf-bmc -i -d 2 -v $verbosity mvs_with_timeouts4 mvs_bounds1  -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 -l mvs_timeout_bounds1

echo "proving mvs_bounds3"
echo sal-inf-bmc -i -d 2 -v $verbosity mvs_with_timeouts4 mvs_bounds2  -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 -l mvs_timeout_bounds2
sal-inf-bmc -i -d 2 -v $verbosity mvs_with_timeouts4 mvs_bounds2  -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 -l mvs_timeout_bounds2


echo "proving agreement"
echo sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 agreement -l y_init1 -l y_invar1 -l y_init3 -l y_invar3 -l pre_y_init1 \
 -l pre_y_invar1 -l pre_y_init3 -l pre_y_invar3 -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 \
 -l mvs_timeout_bounds1 -l mvs_timeout_bounds2 -l mvs_bounds1 -l mvs_bounds2
sal-inf-bmc -i -d 1 -v $verbosity mvs_with_timeouts4 agreement -l y_init1 -l y_invar1 -l y_init3 -l y_invar3 -l pre_y_init1 \
 -l pre_y_invar1 -l pre_y_init3 -l pre_y_invar3 -l fcm_timeout_bounds1 -l fcm_timeout_bounds3 \
 -l mvs_timeout_bounds1 -l mvs_timeout_bounds2 -l mvs_bounds1 -l mvs_bounds2





