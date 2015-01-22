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

  /** Add an assertion f to the solver */
  void add(expr::term_ref f);

  /** Check the assertions for satisfiability */
  result check();

  /** Get the model */
  void get_model(expr::model& m) const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /**
   * Generalize the last call to check assuming the result was SAT. The
   * variables vars are eliminated from the assertions.
   */
  void generalize(const std::vector<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out);

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);
};

}
}

#endif
