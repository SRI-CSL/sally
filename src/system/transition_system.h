/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
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
  state_formula* d_initial_states;

  /** The transition formula */
  transition_formula* d_transition_relation;

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

  /** Invariants */
  std::vector<state_formula*> d_invariants;

  const std::vector<state_formula*>& get_invariants() const {
    return d_invariants;
  }

  /** Get the assumptions in one state formula */
  expr::term_ref get_assumption() const;

public:

  transition_system(const state_type* state_type, state_formula* initial_states, transition_formula* transition_relation)
  : d_state_type(state_type)
  , d_initial_states(initial_states)
  , d_transition_relation(transition_relation)
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

  /** Add an invariant to the system (takes over the pointer) */
  void add_invariant(state_formula* invariant);

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const transition_system& T);

}
}
