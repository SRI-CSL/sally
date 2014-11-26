/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "smt/solver.h"

namespace sal2 {
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
  yices2(expr::term_manager& tm, const options& opts);

  /** Destructor */
  ~yices2();

  /** Add an assertion f to the solver */
  void add(expr::term_ref f);

  /** Check the assertions for satisfiability */
  result check();

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /** Generalize the last call to check assuming the result was SAT */
  expr::term_ref generalize();

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);
};

}
}
