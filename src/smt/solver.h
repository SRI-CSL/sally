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
 *
 * Formulas being solved are of the form (A(x) and B(x, y) and C(y)). When
 * generalizing we eliminate the variables y. When intepolating we eliminate
 * the variables x.
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

protected:

  /** All x variables */
  std::set<expr::term_ref> d_x_variables;

  /** All y variables */
  std::set<expr::term_ref> d_y_variables;

public:

  /** Result of the check */
  enum result {
    /** Formula is satisfiable */
    SAT,
    /** Formula is unsatisfiable */
    UNSAT,
    /** The result is unknown */
    UNKNOWN
  };

  /** Class of the formula */
  enum formula_class {
    CLASS_A,
    CLASS_B,
    CLASS_C
  };

  /** Solver features */
  enum feature {
    GENERALIZATION,
    INTERPOLATION
  };

  /**
   * Mark a variable as belonging to x (class A). This is permanent, i.e it
   * the variable will still belong to x after a pop.
   */
  virtual
  void add_x_variable(expr::term_ref x_var);

  template<typename iterator>
  void add_x_variables(iterator begin, iterator end) {
    for(; begin != end; ++ begin) {
      add_x_variable(*begin);
    }
  }

  /**
   * Mark a variable as belonging to y (class B).This is permanent, i.e it
   * the variable will still belong to x after a pop.
   */
  virtual
  void add_y_variable(expr::term_ref y_var);

  template<typename iterator>
  void add_y_variables(iterator begin, iterator end) {
    for(; begin != end; ++ begin) {
      add_y_variable(*begin);
    }
  }

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

  /** Check if the solver supports a feature */
  virtual
  bool supports(feature f) const {
    return false;
  }

  /** Assert the formula */
  virtual
  void add(expr::term_ref f, formula_class f_class) = 0;

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
   * Generalize the last call to check assuming the result was SAT, i.e.
   * return the a formula G satisfiable in the current model such that
   *
   *   G(x) => \exists y . A(x) and B(x, y) and C(y).
   *
   * Variables of class C are eliminated from the assertions.
   */
  virtual
  void generalize(std::vector<expr::term_ref>& projection_out) {
    throw exception("generalize() not supported by solver " + d_name);
  }

  /**
   * Same as above, but returns a single expressions.
   */
  expr::term_ref generalize();

  /**
   * Interpolate an unsatisfiable answer, i.e. return the formula such that
   *
   *   A(x) and B(x, y) => I(y)     and     I(y) => not C(y).
   */
  virtual
  void interpolate(std::vector<expr::term_ref>& out) {
    throw exception("interpolate() not supported by solver " + d_name);
  };

  /**
   * Same as above, but returns a single expressions.
   */
  expr::term_ref interpolate();
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

std::ostream& operator << (std::ostream& out, solver::formula_class fc);

}
}
