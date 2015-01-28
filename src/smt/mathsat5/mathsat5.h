/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_MATHSAT5

#include "smt/solver.h"

namespace sal2 {
namespace smt {

class mathsat5_internal;

/**
 * Yices SMT solver.
 */
class mathsat5 : public solver {

  /** Internal yices data */
  mathsat5_internal* d_internal;

public:

  /** Constructor */
  mathsat5(expr::term_manager& tm, const options& opts);

  /** Destructor */
  ~mathsat5();

  /** Features */
  bool supports(feature f) const {
    switch (f) {
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

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);

  /** Interpolate the last sat result (trivial) */
  void generalize(std::vector<expr::term_ref>& out);
};

}
}

#endif
