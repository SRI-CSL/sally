/*
 * smt_solver.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"

namespace sal2 {
namespace smt {

/**
 * SMT solver interface for solving queries of the form
 *
 *  F(x, y) = A(x) & T(x, y) & B(y)
 *
 * If F is sat, we can generalize in terms of x.
 * If F is unsat, we can get an interpolant in terms of y.
 */
class solver {

  expr::term_manager& d_tm;

public:

  enum result {
    SAT,
    UNSAT,
    UNKNOWN
  };

  /** Construct with the given term manager */
  solver(expr::term_manager& tm)
  : d_tm(tm)
  {}

  virtual ~solver() = 0;

  /** Assert the formula */
  void assert_formula(const expr::term_ref& f) = 0;

  /** Check for satisfiability */
  result check_sat() = 0;

  /** Generalize a satisfiable answer */
  expr::term_ref_strong generalize() = 0;

  /**
   * Interpolate an unsatisfiable answer, i.e. get
   */
  void interpolate(std::vector<expr::term_ref_strong>& ) = 0;
};

/**
 * Factory for creating SMT solvers.
 */
class factory {
public:
  /**
   * Create a solver.
   * @param id id of the solver
   * @param tm the term manager
   */
  static solver* mk_solver(std::string id, expr::term_manager& tm);
};



}
}
