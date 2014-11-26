/*
 * smt_solver.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "utils/exception.h"
#include "utils/options.h"

namespace sal2 {
namespace smt {

/**
 * SMT solver interface for solving queries.
 */
class solver {

protected:

  /** The term manager for the solver */
  expr::term_manager& d_tm;

  /** Name of the solver */
  std::string d_name;

  /** The options */
  const options& d_opts;

  /** Get the options */
  const options& get_options() const {
    return d_opts;
  }

public:

  enum result {
    SAT,
    UNSAT,
    UNKNOWN
  };

  /** Construct with the given term manager */
  solver(expr::term_manager& tm, std::string name, const options& opts)
  : d_tm(tm)
  , d_name(name)
  , d_opts(opts)
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
   * @prarm opts the options
   */
  static solver* mk_solver(std::string id, expr::term_manager& tm, const options& opts);
};



}
}
