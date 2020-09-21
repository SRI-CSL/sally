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

#ifdef WITH_GENERIC_SOLVER

#include "smt/solver.h"

#include <vector>

namespace sally {
namespace smt {

class generic_solver_internal;

/**
 * A generic solver that we interact through SMT2 file interface.
 */
class generic_solver : public solver {

  /** Internal implementation */
  generic_solver_internal* d_internal;

public:

  /** Constructor */
  generic_solver(expr::term_manager& tm, const options& opts, utils::statistics& stats);

  /** Destructor */
  ~generic_solver();

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

}
}

#endif