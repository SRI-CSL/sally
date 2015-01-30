/*
 * transition_system.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#pragma once

#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include <iosfwd>

namespace sally {
namespace system {

class transition_system {

  /** The state information */
  const state_type* d_state_type;

  /** The intial states */
  const state_formula* d_initial_states;

  /** The transition formula */
  std::vector<const transition_formula*> d_transition_relation;

  /** Any assumptions */
  std::vector<state_formula*> d_assumptions;

  /** Get all the individual assumptions */
  const std::vector<state_formula*>& get_assumptions() const {
    return d_assumptions;
  }

  /** Do we have assumptions */
  bool has_assumptions() const {
    return !d_assumptions.empty();
  }

  /** Get the assumptions in one state formula */
  expr::term_ref get_assumption() const;

public:

  transition_system(const state_type* state_type, const state_formula* initial_states, const std::vector<const transition_formula*>& transition_relation)
  : d_state_type(state_type)
  , d_initial_states(initial_states)
  , d_transition_relation(transition_relation)
  {}

  transition_system(const transition_system& T)
  : d_state_type(T.d_state_type)
  , d_initial_states(T.d_initial_states)
  , d_transition_relation(T.d_transition_relation)
  {}

  ~transition_system();

  /** Get the state type */
  const state_type* get_state_type() const {
    return d_state_type;
  }

  /** Get the initial states */
  expr::term_ref get_initial_states() const;

  /** Get the whole transition relation (disjunction) */
  expr::term_ref get_transition_relation() const;

  /** Add an assumption on the state type (takes over the pointer) */
  void add_assumption(state_formula* assumption);

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const transition_system& T);

}
}
