/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2

#include "smt/solver.h"

namespace sally {
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

  /** Features */
  bool supports(feature f) const {
    switch (f) {
    case GENERALIZATION:
      return true;
    default:
      return false;
    }
  }

  /** Add an assertion f to the solver */
  void add(expr::term_ref f, formula_class f_class);

  /** Add an variable */
  void add_variable(expr::term_ref var, variable_class f_class);

  /** Check the assertions for satisfiability */
  result check();

  /** Get the model */
  void get_model(expr::model& m) const;

  /** Push the solving context */
  void push();

  /** Pop the solving context */
  void pop();

  /**
   * Generalize the last call to check assuming the result was SAT.
   */
  void generalize(generalization_type type, std::vector<expr::term_ref>& projection_out);

  /** Term collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();
};

}
}

#endif
