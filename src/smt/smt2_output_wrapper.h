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

#include <fstream>

namespace sally {
namespace smt {

/**
 * A solver that wraps another solver and outputs the queries to a file.
 */
class smt2_output_wrapper : public solver {

  /** Solver actually used */
  solver* d_solver;

  /** Output file */
  std::string d_output_filename;

  /** Output */
  std::ofstream d_output;

  /** Total number of assertions */
  int d_total_assertions_count;

  struct assertion {
    size_t index;
    expr::term_ref f;
    formula_class f_class;
    assertion(int index, expr::term_ref f, formula_class f_class)
    : index(index), f(f), f_class(f_class) {}
  };

  /** Keep track of assertions for interpolation groups */
  std::vector<assertion> d_assertions;

  /** Size of assertions by push */
  std::vector<size_t> d_assertions_size;

  /** Have variables been added */
  bool d_vars_added;

public:

  /** Takes over the solver and will destruct it on destruction */
  smt2_output_wrapper(expr::term_manager& tm, const options& opts, utils::statistics& stats, solver* solver, std::string filename);
  ~smt2_output_wrapper();

  bool supports(feature f) const;
  void add(expr::term_ref f, formula_class f_class);
  result check();
  expr::model::ref get_model() const;
  void push();
  void pop();
  int get_scope() const;
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);
  void generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out);
  void interpolate(std::vector<expr::term_ref>& out);
  void get_unsat_core(std::vector<expr::term_ref>& out);
  void add_variable(expr::term_ref var, variable_class f_class);
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

}
}
