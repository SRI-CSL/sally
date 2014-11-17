/*
 * state_formula.h
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#pragma once

#include <string>
#include <vector>
#include <cassert>

#include "expr/term.h"

namespace sal2 {
namespace expr {

/**
 * The state just keeps the list of variables of the state, including
 */
class state_type {

  term_ref_strong d_state_type;

  std::vector<std::string> names;
  std::vector<term_ref_strong> vars;

};


class state_formula {

  /** The state information */
  term_ref_strong d_state_type;

  /** The actual formula */
  term_ref_strong d_formula;

public:

  state_formula(term_manager& tm, term_ref state_type, term_ref formula)
  : d_state_type(tm, state_type)
  , d_formula(tm, formula)
  {}

  /** Get the state formula */
  term_ref get_formula() const {
    return d_formula;
  }

  term_ref get_state_type() const {
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

class state_transition_formula {

  /** The state information */
  term_ref_strong d_state_type;

  /** The actual formula */
  term_ref_strong d_transition_formula;

public:

  state_transition_formula(term_manager& tm, term_ref state_type, term_ref transition_formula)
  : d_state_type(tm, state_type)
  , d_transition_formula(tm, transition_formula)
  {}

  /** Get the state formula */
  term_ref get_transition_formula() const {
    return d_transition_formula;
  }

  term_ref get_state_type() const {
    return d_state_type;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const state_transition_formula& sf) {
  sf.to_stream(out);
  return out;
}

}
}
