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

/** A functor that constructs a new solver on each call */
class solver_constructor {
public:
  virtual ~solver_constructor() {};
  virtual solver* mk_solver() = 0;
};

/**
 * A solver that wraps another solver and doesn't use push/pop. Instead the
 * solver is created on each check and all assertions are added.
 */
class incremental_wrapper : public solver {

  /** The solver we're simulating */
  solver_constructor* d_constructor;

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

  /** Instance */
  static size_t d_instance;

public:

  incremental_wrapper(std::string name, expr::term_manager& tm, const options& opts, solver_constructor* constructor);
  ~incremental_wrapper();

  bool supports(feature f) const;
  void add(expr::term_ref f, formula_class f_class);
  result check();
  void get_model(expr::model& m) const;
  void push();
  void pop();
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);
  void interpolate(std::vector<expr::term_ref>& out);
  void get_unsat_core(std::vector<expr::term_ref>& out);
  void gc_collect(const expr::gc_relocator& gc_reloc);
};

}
}
