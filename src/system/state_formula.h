/*
 * state_formula.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/state_type.h"

namespace sal2 {
namespace system {

/**
 * A formula where over a state type.
 */
class state_formula {

  /** The state variables */
  state_type d_state_type;

  /** The formula itself */
  expr::term_ref_strong d_state_formula;

public:

  state_formula(expr::term_manager& tm, const state_type& st, expr::term_ref formula)
  : d_state_type(st)
  , d_state_formula(tm, formula)
  {}

  state_formula(const state_formula& sf)
  : d_state_type(sf.d_state_type)
  , d_state_formula(sf.d_state_formula)
  {}

  /** Get the state formula */
  expr::term_ref get_formula() const {
    return d_state_formula;
  }

  /** Get the state type */
  const state_type& get_state_type() const {
    return d_state_type;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const state_formula& sf) {
  sf.to_stream(out);
  return out;
}


}
}
