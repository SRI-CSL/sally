/*
 * smt2_solver.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "smt/solver.h"

#include <vector>

namespace sal2 {
namespace smt {

class smt2_solver_internal;

/**
 * A generic solver that we interact through SMT2 file interface.
 */
class smt2_solver : public solver {

  smt2_solver_internal* d_internal;

public:

  smt2_solver(expr::term_manager& tm);
  ~smt2_solver();

  /** Add an assertion f to the solver */
  void add(expr::term_ref f);

  /** Check the assertions for satisfiability */
  result check();

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();
};

}
}
