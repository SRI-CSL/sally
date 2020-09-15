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

#include "smt/solver.h"
#include "expr/model.h"

namespace sally {
namespace smt {

class yices2_internal;

/**
 * Yices SMT solver.
 */
class yices2 : public solver {

  /** Internal yices data */
  yices2_internal* d_internal;

public:

  /** Constructor */
  yices2(expr::term_manager& tm, const options& opts, utils::statistics& stats);

  /** Destructor */
  ~yices2();

  /** Features */
  bool supports(feature f) const;

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Add an variable */
  void add_variable(expr::term_ref var, variable_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Consistent? */
  bool is_consistent();

  /** Get the model */
  expr::model::ref get_model() const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /**
   * Generalize the last call to check assuming the result was SAT.
   */
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);

  /**
   * Generalize the given model.
   */
  void generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out);

  /**
   * Interpolate an unsatisfiable answer.
   */
  void interpolate(std::vector<expr::term_ref>& out);

  /** Set the hint */
  void set_hint(expr::model::ref m);

  /** Term collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();
};

}
}

#endif
