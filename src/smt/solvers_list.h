/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

//
// ADD ALL THE ENGINES HERE
//

#include "smt/yices2/yices2_info.h"
#include "smt/mathsat5/mathsat5_info.h"
#include "smt/z3/z3_info.h"
#include "smt/opensmt2/opensmt2_info.h"
#include "smt/y2m5/y2m5_info.h"
#include "smt/y2z3/y2z3_info.h"
#include "smt/y2o2/y2o2_info.h"
#include "smt/generic/generic_solver_info.h"
#include "smt/dreal/dreal_info.h"
#include "smt/d4y2/d4y2_info.h"

sally::smt::solver_data::solver_data() {
#ifdef WITH_YICES2
  add_module_info<yices2_info>();
#endif
#ifdef WITH_MATHSAT5
  add_module_info<mathsat5_info>();
#endif
#ifdef WITH_Z3
  add_module_info<z3_info>();
#endif
#ifdef WITH_YICES2
#ifdef WITH_MATHSAT5
  add_module_info<y2m5_info>();
#endif
#endif
#ifdef WITH_YICES2
#ifdef WITH_Z3
  add_module_info<y2z3_info>();
#endif
#endif
#ifdef WITH_OPENSMT2
  add_module_info<opensmt2_info>();
#ifdef WITH_YICES2
  add_module_info<y2o2_info>();
#endif // WITH_YICES2
#endif // WITH_OPENSMT2
  add_module_info<generic_solver_info>();
#ifdef WITH_DREAL
  add_module_info<dreal_info>();
#endif   
#ifdef WITH_YICES2
#ifdef WITH_DREAL
  add_module_info<d4y2_info>();
#endif
#endif
}

std::string sally::smt::factory::get_default_solver_id() {
  if (s_default_solver.empty()) {
#ifdef WITH_YICES2
    s_default_solver = yices2_info::get_id();
#elif defined WITH_Z3
    s_default_solver = z3_info::get_id();
#elif defined WITH_MATHSAT5
    s_default_solver = mathsat5_info::get_id();
#elif defined WITH_DREAL
    s_default_solver = dreal_info::get_id();
#else
    s_default_solver = generic_solver_info::get_id();
#endif
  }
  return s_default_solver;
}


