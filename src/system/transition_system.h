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

#include "state_type.h"
#include "state_formula.h"
#include "transition_formula.h"
#include "trace_helper.h"

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

  /** The invariant formula */
  state_formula* d_invariant;

  /** Any assumptions */
  std::vector<state_formula*> d_assumptions_state;

  /** Get all the individual assumptions */
  const std::vector<state_formula*>& get_state_assumptions() const {
    return d_assumptions_state;
  }

  /** Do we have assumptions */
  bool has_state_assumptions() const {
    return !d_assumptions_state.empty();
  }

  /** Any assumptions */
  std::vector<transition_formula*> d_assumptions_transition;

  /** Get all the individual assumptions */
  const std::vector<transition_formula*>& get_transition_assumptions() const {
    return d_assumptions_transition;
  }

  /** Do we have assumptions */
  bool has_transition_assumptions() const {
    return !d_assumptions_transition.empty();
  }


  /** Get the assumptions in one state formula */
  expr::term_ref get_state_assumption() const;

  /** Get the assumptions in one transition formula */
  expr::term_ref get_transition_assumption() const;


  /** The trace helper for this transition system */
  trace_helper* d_trace_helper;

public:

  transition_system(const state_type* state_type, state_formula* initial_states, transition_formula* transition_relation);
  transition_system(const state_type* state_type, state_formula* initial_states, transition_formula* transition_relation, state_formula* invariant);
  ~transition_system();

  /** Get the state type */
  const state_type* get_state_type() const {
    return d_state_type;
  }

  /** Get the initial states */
  expr::term_ref get_initial_states() const;

  /** Get the whole transition relation (disjunction) */
  expr::term_ref get_transition_relation() const;

  /** Get the whole invariant (conjunction) */
  expr::term_ref get_invariant() const;

  /** Get the trace helper */
  trace_helper* get_trace_helper() const;

  /** Add an assumption on the state type (takes over the pointer) */
  void add_assumption(state_formula* assumption);

  /** Add an assumption on the state type (takes over the pointer) */
  void add_assumption(transition_formula* assumption);

  /** Print it to the stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator << (std::ostream& out, const transition_system& T);

}
}
