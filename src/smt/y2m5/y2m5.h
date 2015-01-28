/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2
#ifdef WITH_MATHSAT5

#include "smt/solver.h"

namespace sal2 {
namespace smt {

class yices2;
class mathsat5;

/**
 * Combination solver: Yices for generalization, MathSAT5 for interpolation.
 * Note that all checks are done twice, so expect penalty.
 */
class y2m5 : public solver {

  yices2* d_yices2;
  mathsat5* d_mathsat5;

  static size_t s_instance;

public:

  void add_x_variable(expr::term_ref x_var);
  void add_y_variable(expr::term_ref y_var);

  /** Constructor */
  y2m5(expr::term_manager& tm, const options& opts);

  /** Destructor */
  ~y2m5();

  /** Features */
  bool supports(feature f) const {
    switch (f) {
    case GENERALIZATION:
      return true;
    case INTERPOLATION:
      return true;
    default:
      return false;
    }
  }

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Get the model */
  void get_model(expr::model& m) const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /** Generalize the last call to check assuming the result was SAT. */
  void generalize(std::vector<expr::term_ref>& out);

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);
};

}
}

#endif
#endif
