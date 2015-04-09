/*
 * smt2_output_wrapper.h
 *
 *  Created on: Feb 23, 2015
 *      Author: dejan
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

public:

  /** Takes over the solver and will destruct it on destruction */
  smt2_output_wrapper(expr::term_manager& tm, const options& opts, solver* solver, std::string filename);
  ~smt2_output_wrapper();

  bool supports(feature f) const;
  void add(expr::term_ref f, formula_class f_class);
  result check();
  void get_model(expr::model& m) const;
  void push();
  void pop();
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);
  void interpolate(std::vector<expr::term_ref>& out);
  void get_unsat_core(std::vector<expr::term_ref>& out);

  void add_x_variable(expr::term_ref x_var);
  void add_y_variable(expr::term_ref y_var);

  void gc_collect(const expr::gc_info& gc_reloc);

};

}
}
