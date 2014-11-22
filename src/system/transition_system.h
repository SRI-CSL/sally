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

namespace sal2 {
namespace system {

class transition_system {

  /** The state information */
  const state_type* d_state_type;

  /** The intial states */
  const state_formula* d_initial_states;

  /** The transition formula */
  std::vector<const transition_formula*> d_transition_relation;

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

  /** Get the state type */
  const state_type* get_state_type() const {
    return d_state_type;
  }

  /** Get the intial states */
  expr::term_ref get_initial_states() const {
    return d_initial_states->get_formula();
  }

  /** Get the number of transitions */
  size_t get_transitions_count() const {
    return d_transition_relation.size();
  }

  /** Get the transition relation */
  expr::term_ref get_transition(size_t i) const {
    return d_transition_relation[i]->get_formula();
  }

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const transition_system& T);

}
}
