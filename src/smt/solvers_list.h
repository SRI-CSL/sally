/*
 * solvers_list.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#pragma once

//
// ADD ALL THE ENGINES HERE
//

#include "smt/yices2/yices2_info.h"
#include "smt/generic/generic_solver_info.h"

sal2::smt::solver_data::solver_data() {
  add_module_info<yices2_info>();
  add_module_info<generic_solver_info>();
}



