/*
 * smt_solver.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/model.h"
#include "expr/gc_participant.h"
#include "utils/exception.h"
#include "utils/options.h"
#include "utils/name_transformer.h"

namespace sally {
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
 * Formulas being solved are of the form (A(x) and T(x, y) and B(y)). When
 * generalizing we eliminate the variables y. When intepolating we eliminate
 * the variables x.
 */
class solver : public expr::gc_participant {

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
    CLASS_T,
    CLASS_B
  };

  /** Solver features */
  enum feature {
    GENERALIZATION,
    INTERPOLATION,
    UNSAT_CORE,
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
  : gc_participant(tm)
  , d_name(name)
  , d_tm(tm)
  , d_opts(opts)
  {}

  /** Construct with the given context */
  solver(std::string name, const solver_context& ctx)
  : gc_participant(ctx.tm)
  , d_name(name)
  , d_tm(ctx.tm)
  , d_opts(ctx.opts)
  {}

  virtual
  ~solver() {};

  /** Get the solver name */
  std::string get_name() const {
    return d_name;
  }

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

  /** Check the model if the formula is SAT (for debug purposes only) */
  virtual
  void check_model() {
    throw exception("check_model() not supported by solver " + d_name);
  }

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

  enum generalization_type {
    GENERALIZE_FORWARD,
    GENERALIZE_BACKWARD
  };

  /**
   * Generalize the last call to check assuming the result was SAT, i.e.
   * return the a formula G satisfiable in the current model M such that
   *
   *   G(x) => \exists y . (T(x, y) and B(y)).
   *
   * This is the dual of interpolation, i.e. we get a G such that
   *
   *   A and G are consistent (both satisfied by the model M)
   *   G implies \exists y . (T(x, y) and B(y)).
   *
   * Variables of class B are eliminated from the assertions.
   */
  virtual
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out) {
    throw exception("generalize() not supported by solver " + d_name);
  }

  /**
   * Same as above, but returns a single expressions.
   */
  expr::term_ref generalize(generalization_type type);

  /**
   * Interpolate an unsatisfiable answer, i.e. return the formula such that
   *
   *   A(x, y) => I(y)     and     I(y) => B(y).
   */
  virtual
  void interpolate(std::vector<expr::term_ref>& out) {
    throw exception("interpolate() not supported by solver " + d_name);
  };

  /**
   * Get the unsat core of an unsatisfiable answer, i.e. return a set of
   * assertions that are unsat.
   */
  virtual
  void get_unsat_core(std::vector<expr::term_ref>& out) {
    throw exception("get_unsat_core() not supported by solver " + d_name);
  }

  /**
   * Same as above, but returns a single expressions.
   */
  expr::term_ref interpolate();

  /**
   * Collect any garbage.
   */
  virtual
  void gc() {}
};


std::ostream& operator << (std::ostream& out, solver::result result);

/**
 * Push/pop scope manager.
 */
class solver_scope {
  size_t d_pushes;
  solver* d_solver;
public:
  solver_scope(solver* s): d_pushes(0), d_solver(s) {}
  ~solver_scope() { clear(); }
  void clear() { while (d_pushes > 0) { d_solver->pop(); d_pushes --; } }
  void push() { d_solver->push(); d_pushes ++; }
  void pop() { d_solver->pop(); d_pushes --; }
  size_t get_scope() { return d_pushes; }
};

std::ostream& operator << (std::ostream& out, solver::formula_class fc);

/** Name transformer for any output to smt2 */
class smt2_name_transformer : public utils::name_transformer {
public:
  std::string apply(std::string id) const {
    return "|" + id + "|";
  }
};

}
}
