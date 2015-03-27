/*
 * state_formula.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/state_type.h"

#include <iosfwd>

namespace sally {
namespace system {

/**
 * A formula where over a state type.
 */
class state_formula {

  /** The state variables */
  const state_type* d_state_type;

  /** The formula itself */
  expr::term_ref_strong d_state_formula;

public:

  /**
   * Construct a state formula over the state type with the explicit formula.
   * It also registers itself with the state type.
   */
  state_formula(expr::term_manager& tm, const state_type* st, expr::term_ref formula);

  /** Destruct and unregister. */
  ~state_formula();

  /** Get the state formula */
  expr::term_ref get_formula() const {
    return d_state_formula;
  }

  /** Get the state type */
  const state_type* get_state_type() const {
    return d_state_type;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const state_formula& sf);

}
}
