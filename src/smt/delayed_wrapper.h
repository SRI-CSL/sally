/*
 * incremental_wrapper.h
 *
 *  Created on: Feb 8, 2015
 *      Author: dejan
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

public:

  /** Takes over the solver and will destruct it on destruction */
  delayed_wrapper(std::string name, expr::term_manager& tm, const options& opts, solver* s);
  ~delayed_wrapper();

  bool supports(feature f) const;
  void add(expr::term_ref f, formula_class f_class);
  result check();
  void get_model(expr::model& m) const;
  void push();
  void pop();
  void generalize(std::vector<expr::term_ref>& projection_out);
  void interpolate(std::vector<expr::term_ref>& out);

  void add_x_variable(expr::term_ref x_var);
  void add_y_variable(expr::term_ref y_var);
};

}
}
