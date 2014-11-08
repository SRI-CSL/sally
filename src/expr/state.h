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

class state_type {

  /** Map from variable names to their types */
  std::map<std::string, term_ref> d_var_to_type_map;

  /** The id of the state */
  std::string d_name;

public:

  state_type(std::string name)
  : d_name(name)
  {}

  /** Get the name of the state type */
  std::string get_name() const {
    return d_name;
  }

  /** Ads a new variable to the state */
  void add_variable(std::string name, term_ref type) {
    d_var_to_type_map[name] = type;
  }

  /** Check if the variable is in the state */
  bool contains(std::string name) const {
    return d_var_to_type_map.find(name) != d_var_to_type_map.end();
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const state_type& st) {
  st.to_stream(out);
  return out;
}

class state_formula {

  /** The state information */
  const state_type& d_state_type;

  /** The actual formula */
  term_ref_strong d_formula;

public:

  state_formula(const state_type& state_type)
  : d_state_type(state_type)
  {}

  /** Get the state formula */
  term_ref_strong get_formula() const {
    return d_formula;
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
  const state_type& d_state_type;

  /** The transition formula */
  term_ref_strong d_transition_formula;

public:

  state_transition_formula(const state_type& state_type)
  : d_state_type(state_type)
  {}

  /** Get the transition relation */
  term_ref_strong get_formula() const {
    return d_transition_formula;
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const state_transition_formula& stf) {
  stf.to_stream(out);
  return out;
}


}
}
