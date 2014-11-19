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
 * A state type identified by it's id (name) and it's type
 */
class state_type {

public:

  /** Class of state variables */
  enum var_class {
    /** Current state */
    CURRENT,
    /** Next state */
    NEXT
  };

  /** String representation of the variable class */
  static std::string to_string(var_class vc);

  /** Create a new state type of the given type and name */
  state_type(term_manager& tm, std::string id, term_ref type);

  /** Print the state type to stream */
  void to_stream(std::ostream& out) const;

  /** Get the state variable(s) of the class */
  term_ref get_state(var_class vc) const;

private:

  /** The name of the type */
  std::string d_id;

  /** The actual type describing the state */
  term_ref_strong d_type;

  /** The current state */
  term_ref_strong d_current_state;

  /** The next state */
  term_ref_strong d_next_state;
};

inline
std::ostream& operator << (std::ostream& out, const state_type& st) {
  st.to_stream(out);
  return out;
}

/**
 * A formula where over a state type.
 */
class state_formula {

  /** The state variables */
  state_type d_state_type;

  /** The formula itself */
  term_ref_strong d_state_formula;

public:

  state_formula(term_manager& tm, const state_type& st, term_ref formula)
  : d_state_type(st)
  , d_state_formula(tm, formula)
  {}

  state_formula(const state_formula& sf)
  : d_state_type(sf.d_state_type)
  , d_state_formula(sf.d_state_formula)
  {}

  /** Get the state formula */
  term_ref get_formula() const {
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
