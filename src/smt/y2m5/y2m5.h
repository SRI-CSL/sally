/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2
#ifdef WITH_MATHSAT5

#include "smt/solver.h"

namespace sally {
namespace smt {

/**
 * Combination solver: Yices for generalization, MathSAT5 for interpolation.
 * Note that all checks are done twice, so expect penalty.
 */
class y2m5 : public solver {

  solver* d_yices2;
  solver* d_mathsat5;

  static size_t s_instance;

  /** Last result of mathsat */
  result d_last_mathsat5_result;

  /* Last result of yices */
  result d_last_yices2_result;

public:

  void add_x_variable(expr::term_ref x_var);
  void add_y_variable(expr::term_ref y_var);

  /** Constructor */
  y2m5(expr::term_manager& tm, const options& opts);

  /** Destructor */
  ~y2m5();

  /** Features */
  bool supports(feature f) const;

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Get the model */
  void get_model(expr::model& m) const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /** Generalize the last call to check assuming the result was SAT. */
  void generalize(generalization_type type, std::vector<expr::term_ref>& out);

  /** Interpolate the last UNSAT result */
  void interpolate(std::vector<expr::term_ref>& out);

  /** Unsat core of the last UNSAT result */
  void get_unsat_core(std::vector<expr::term_ref>& out);

  /** Term collection (nothing to do) */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();
};

}
}

#endif
#endif
