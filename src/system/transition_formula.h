/*
 * transition_formula.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/state_type.h"

namespace sal2 {
namespace system {

class transition_formula {

  /** The state information */
  const state_type* d_state_type;

  /** The actual formula */
  expr::term_ref_strong d_transition_formula;

public:

  transition_formula(expr::term_manager& tm, const state_type* st, expr::term_ref tf)
  : d_state_type(st)
  , d_transition_formula(tm, tf)
  {}

  /** Get the state formula */
  expr::term_ref get_formula() const {
    return d_transition_formula;
  }

  const state_type*  get_state_type() const {
    return d_state_type;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const transition_formula& sf) {
  sf.to_stream(out);
  return out;
}


}
}
