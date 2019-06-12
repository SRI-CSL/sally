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

#ifdef WITH_YICES2
#ifdef WITH_DREAL

#include "smt/solver.h"
#include "expr/term.h"
#include "expr/model.h"

#include <vector>

namespace sally {
namespace smt {

/**
 * Combination solver: Yices for generalization, MathSAT5 for interpolation.
 * Note that all checks are done twice, so expect penalty.
 */
class d4y2 : public solver {

  solver* d_dreal4;
  solver* d_yices2;

  static size_t s_instance;

  /** Last result of mathsat */
  result d_last_dreal4_result;

  /* Last result of yices */
  result d_last_yices2_result;

public:

  /** Constructor */
  d4y2(expr::term_manager& tm, const options& opts, utils::statistics& stats);

  /** Destructor */
  ~d4y2();

  /** Features */
  bool supports(feature f) const;

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Add a variable */
  void add_variable(expr::term_ref var, variable_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Get the model */
  expr::model::ref get_model() const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /** Generalize the last call to check assuming the result was SAT. */
  void generalize(generalization_type type, std::vector<expr::term_ref>& out);

  /** Generalize the model */
  void generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out);

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);

  /** Unsat core of the last UNSAT result */
  void get_unsat_core(std::vector<expr::term_ref>& out);

  /** Term collection (nothing to do) */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();
};

}
}

#endif
#endif
