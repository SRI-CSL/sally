/*
 * smt_solver.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "utils/exception.h"

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

protected:

  /** The term manager for the solver */
  expr::term_manager& d_tm;

  /** Name of the solver */
  std::string d_name;

public:

  enum result {
    SAT,
    UNSAT,
    UNKNOWN
  };

  /** Construct with the given term manager */
  solver(expr::term_manager& tm, std::string name)
  : d_tm(tm)
  , d_name(name)
  {}

  virtual
  ~solver() {};

  /** Assert the formula */
  virtual
  void add(expr::term_ref f) = 0;

  /** Check for satisfiability */
  virtual
  result check() = 0;

  /** Push a context */
  virtual
  void push() {
    throw exception("push() not supported by solver " + d_name);
  }

  /** Pop a context */
  virtual
  void pop() {
    throw exception("pop() not supported by solver " + d_name);
  }

  /** Generalize a satisfiable answer */
  virtual
  expr::term_ref generalize() {
    throw exception("generalize() not supported by solver " + d_name);
  }

  /** Interpolate an unsatisfiable answer */
  virtual
  void interpolate(std::vector<expr::term_ref>& ) {
    throw exception("interpolate() not supported by solver " + d_name);
  };
};

std::ostream& operator << (std::ostream& out, solver::result result);

/**
 * Push/pop scope manager.
 */
class solver_scope {
  int d_pushes;
  solver* d_solver;
public:
  solver_scope(solver* s): d_pushes(0), d_solver(s) {}
  ~solver_scope() { while (d_pushes-- > 0) { d_solver->pop(); } }
  void push() { d_solver->push(); d_pushes ++; }
  void pop() { d_solver->pop(); }
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
