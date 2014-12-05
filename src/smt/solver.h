/*
 * smt_solver.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/model.h"
#include "utils/exception.h"
#include "utils/options.h"

namespace sal2 {
namespace smt {

/**
 * The context needed to create a solver.
 */
struct solver_context {
  expr::term_manager& tm;
  const options& opts;
  solver_context(expr::term_manager& tm, const options& opts)
  : tm(tm), opts(opts) {}
};

/**
 * SMT solver interface for solving queries.
 */
class solver {

protected:

  /** Name of the solver */
  std::string d_name;

  /** The term manager for the solver */
  expr::term_manager& d_tm;

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
  solver(std::string name, expr::term_manager& tm, const options& opts)
  : d_name(name)
  , d_tm(tm)
  , d_opts(opts)
  {}

  /** Construct with the given context */
  solver(std::string name, const solver_context& ctx)
  : d_name(name)
  , d_tm(ctx.tm)
  , d_opts(ctx.opts)
  {}

  virtual
  ~solver() {};

  /** Assert the formula */
  virtual
  void add(expr::term_ref f) = 0;

  /** Check for satisfiability */
  virtual
  result check() = 0;

  /** Get the model */
  virtual
  void get_model(expr::model& m) const {
    throw exception("get_model() not supported by solver " + d_name);
  }

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

  /**
   * Generalize the last call to check assuming the result was SAT. The
   * variables vars are eliminated from the assertions.
   */
  virtual
  void generalize(const std::vector<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out) {
    throw exception("generalize() not supported by solver " + d_name);
  }

  /**
   * Same as above, but returns a single expressions.
   */
  expr::term_ref generalize(const std::vector<expr::term_ref>& to_eliminate);

  /** Interpolate an unsatisfiable answer */
  virtual
  void interpolate(std::vector<expr::term_ref>& out) {
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
  void pop() { d_solver->pop(); d_pushes --; }
};

}
}
