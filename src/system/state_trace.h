/*
 * state_trace.h
 *
 *  Created on: Nov 28, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/model.h"
#include "system/state_type.h"

#include <vector>
#include <iosfwd>

namespace sally {
namespace system {

class state_trace {

  /** The state type */
  const state_type* d_state_type;

  /** Sequence of state variables, per step */
  std::vector<expr::term_ref_strong> d_state_variables;

  /** Full model of the trace */
  expr::model d_model;

  /** Returns the state variables for step k */
  expr::term_ref get_state_variable(size_t k);

  /** Returns the term manager */
  expr::term_manager& tm() const;

public:

  /** Create ta trace for the given type */
  state_trace(const state_type* st);

  /**
   * Given a formula in the state type return a state formula in the k-th step.
   */
  expr::term_ref get_state_formula(expr::term_ref sf, size_t k);

  /**
   * Given a transition formula in the state type return a transition formula
   * from i to j step.
   */
  expr::term_ref get_transition_formula(expr::term_ref tf, size_t i, size_t j);

  /**
   * Add model to the trace.
   */
  void add_model(const expr::model& m);

  /**
   * Output the trace to the stream.
   */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const state_trace& trace);

}
}
