/*
 * smt2_solver.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "smt/solver.h"

#include <vector>

namespace sally {
namespace smt {

class generic_solver_internal;

/**
 * A generic solver that we interact through SMT2 file interface.
 */
class generic_solver : public solver {

  /** Internal implementation */
  generic_solver_internal* d_internal;

public:

  /** Constructor */
  generic_solver(expr::term_manager& tm, const options& opts);

  /** Destructor */
  ~generic_solver();

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();
};

}
}
