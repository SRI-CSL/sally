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

class state {

public:

  /** Class of state variabels */
  enum var_class {
    /** Current state */
    CURRENT,
    /** Next state */
    NEXT
  };

  /**
   * Return the name of the variable in the given type. If full is true, the
   * id of the state is prepended to the name.
   */
  static
  std::string get_var_name(std::string state_type_id, std::string var_name, var_class vc, bool full);

};

/**
 * A state type identified by it's id (name) and it's type
 */
class state_type {

  /** The name of the type */
  std::string d_id;

  /** The actual structure describing the state */
  term_ref_strong d_type;

public:

  state_type(term_manager& tm, std::string id, term_ref type)
  : d_id(id)
  , d_type(tm, type)
  {}

};

/**
 * A formula where over a state type.
 */
class state_formula {

  /** The state variables */
  std::vector<term_ref_strong> d_state_variables;

  /** The formula itself */
  expr::term_ref_strong d_state_formula;

public:

  state_formula()
  {}

  state_formula(const state_formula& sf)
  : d_state_variables(sf.d_state_variables)
  , d_state_formula(sf.d_state_formula)
  {}

  /** Get the state formula */
  term_ref get_formula() const {
    return d_state_formula;
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
