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

namespace sal2 {
namespace system {

class state_trace {

  /** The state type */
  const state_type* d_state_type;

  /** Sequence of state variables, per step */
  std::vector<expr::term_ref_strong> d_state_variables;

  /** Returns the state variables for step k */
  expr::term_ref get_state_variables(size_t k);

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
   * Given a transition formula in the state type return a transitiong formula
   * from i to j step.
   */
  expr::term_ref get_transition_formula(expr::term_ref tf, size_t i, size_t j);

};


}
}
