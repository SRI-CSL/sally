/*
 * transition_formula.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/state_type.h"

#include <iosfwd>

namespace sal2 {
namespace system {

class transition_formula {

  /** The term manager */
  expr::term_manager& d_tm;

  /** The state information */
  const state_type* d_state_type;

  /** The actual formula */
  expr::term_ref_strong d_transition_formula;

public:

  /** Create a transition formula from the type and the actual formula */
  transition_formula(expr::term_manager& tm, const state_type* st, expr::term_ref tf);

  /** Create a copy of the given formula */
  transition_formula(const transition_formula& tf);

  /** Get the state formula */
  expr::term_ref get_formula() const {
    return d_transition_formula;
  }

  /** Get the state type */
  const state_type*  get_state_type() const {
    return d_state_type;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const transition_formula& sf);

}
}
