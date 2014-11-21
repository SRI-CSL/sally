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
namespace state {

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

  /** Empty state type */
  state_type() {}

  /** Create a new state type of the given type and name */
  state_type(expr::term_manager& tm, std::string id, expr::term_ref type);

  /** Print the state type to stream */
  void to_stream(std::ostream& out) const;

  /** Get the actual type */
  expr::term_ref get_type() const {
    return d_type;
  }

  /** Get the state variable(s) of the class */
  expr::term_ref get_state(var_class vc) const;

  /** Use the namespace for the type (pop the namespace yourself) */
  void use_namespace(expr::term_manager& tm) const;

  /** Use the namespace for the the var class (pop the namespace yourself)  */
  void use_namespace(expr::term_manager& tm, var_class vc) const;

private:

  /** The name of the type */
  std::string d_id;

  /** The actual type describing the state */
  expr::term_ref_strong d_type;

  /** The current state */
  expr::term_ref_strong d_current_state;

  /** The next state */
  expr::term_ref_strong d_next_state;
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

class state_transition_formula {

  /** The state information */
  state_type d_state_type;

  /** The actual formula */
  expr::term_ref_strong d_transition_formula;

public:

  state_transition_formula(expr::term_manager& tm, const state_type& st, expr::term_ref tf)
  : d_state_type(st)
  , d_transition_formula(tm, tf)
  {}

  /** Get the state formula */
  expr::term_ref get_formula() const {
    return d_transition_formula;
  }

  const state_type&  get_state_type() const {
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

class state_transition_system {

  /** The state information */
  state_type d_state_type;

  /** The intial states */
  state_formula d_initial_states;

  /** The transition formula */
  std::vector<state_transition_formula> d_transition_relation;

public:

  state_transition_system(const state_type& state_type, const state_formula& initial_states, const std::vector<state_transition_formula>& transition_relation)
  : d_state_type(state_type)
  , d_initial_states(initial_states)
  , d_transition_relation(transition_relation)
  {}

  state_transition_system(const state_transition_system& T)
  : d_state_type(T.d_state_type)
  , d_initial_states(T.d_initial_states)
  , d_transition_relation(T.d_transition_relation)
  {}

  /** Get the state type */
  const state_type&  get_state_type() const {
    return d_state_type;
  }

  /** Get the intial states */
  expr::term_ref get_initial_states() const {
    return d_initial_states.get_formula();
  }

  /** Get the number of transitions */
  size_t get_transitions_count() const {
    return d_transition_relation.size();
  }

  /** Get the transition relation */
  expr::term_ref get_transition(size_t i) const {
    return d_transition_relation[i].get_formula();
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const state_transition_system& T) {
  T.to_stream(out);
  return out;
}


}
}
