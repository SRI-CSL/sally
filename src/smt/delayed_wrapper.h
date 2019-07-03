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

#include "smt/solver.h"

namespace sally {
namespace smt {

/**
 * A solver that wraps another solver. Instead of adding the assertions
 * immediately, the solver piles them up and adds them only on a check(). This
 * is useful for solvers that are not used all the time, so that we can
 * reduce the overhead of addition and push/pop.
 */
class delayed_wrapper : public solver {

  struct assertion {
    expr::term_ref f;
    formula_class f_class;
    assertion(expr::term_ref f, formula_class f_class)
    : f(f), f_class(f_class) {}
  };

  /** Keep track of assertions */
  std::vector<assertion> d_assertions;

  /** Assertion sizes per push */
  std::vector<size_t> d_assertions_size;

  /** Solver previously used */
  solver* d_solver;

  /** The index of the next assertion to process */
  size_t d_index;

  /** The scope we last processed */
  size_t d_scope;

  /** Flush the assertions */
  void flush();

public:

  /** Takes over the solver and will destruct it on destruction */
  delayed_wrapper(std::string name, expr::term_manager& tm, const options& opts, utils::statistics& stats, solver* s);
  ~delayed_wrapper();

  bool supports(feature f) const;
  void add(expr::term_ref f, formula_class f_class);
  result check();
  void check_model();
  expr::model::ref get_model() const;
  void push();
  void pop();
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);
  void interpolate(std::vector<expr::term_ref>& out);
  void get_unsat_core(std::vector<expr::term_ref>& out);
  void add_variable(expr::term_ref var, variable_class f_class);
  void set_hint(expr::model::ref m);
  void gc_collect(const expr::gc_relocator& gc_reloc);
};

}
}
