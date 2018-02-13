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

#include "system/transition_system.h"

#include <iostream>

namespace sally {
namespace system {

transition_system::transition_system(const state_type* state_type, state_formula* initial_states, transition_formula* transition_relation)
: d_state_type(state_type)
, d_initial_states(initial_states)
, d_transition_relation(transition_relation)
{
  d_trace_helper = new trace_helper(state_type);
}

transition_system::transition_system(const transition_system* ts)
: d_state_type(ts->get_state_type())
, d_initial_states(new state_formula(ts->d_initial_states))
, d_transition_relation(new transition_formula(ts->d_transition_relation))
{
  d_trace_helper = new trace_helper(d_state_type);
}

void transition_system::to_stream(std::ostream& out) const {
  out << "[" << std::endl;
  out << "type: " << *d_state_type << std::endl;
  out << "I: " << d_initial_states->get_formula() << std::endl;
  out << "T: " << d_transition_relation->get_formula() << std::endl;
  out << "]";
}

std::ostream& operator << (std::ostream& out, const transition_system& T) {
  T.to_stream(out);
  return out;
}

expr::term_ref transition_system::get_transition_relation() const {
  std::vector<expr::term_ref> transitions;
  transitions.push_back(d_transition_relation->get_formula());
  expr::term_ref transition = d_state_type->tm().mk_or(transitions);
  if (has_assumptions()) {
    expr::term_ref A = get_assumption();
    expr::term_ref A_next = d_state_type->change_formula_vars(state_type::STATE_CURRENT, state_type::STATE_NEXT, A);
    transition = d_state_type->tm().mk_term(expr::TERM_AND, transition, A, A_next);
  }
  return transition;
}

expr::term_ref transition_system::get_initial_states() const {
  expr::term_ref I = d_initial_states->get_formula();
  if (has_assumptions()) {
    I = d_state_type->tm().mk_term(expr::TERM_AND, I, get_assumption());
  }
  return I;
}

void transition_system::add_assumption(state_formula* assumption) {
  d_assumptions.push_back(assumption);
}

void transition_system::add_invariant(state_formula* invariant) {
  d_invariants.push_back(invariant);
}

expr::term_ref transition_system::get_assumption() const {
  std::vector<expr::term_ref> assumption_terms;
  for (size_t i = 0; i < d_assumptions.size(); ++ i) {
    assumption_terms.push_back(d_assumptions[i]->get_formula());
  }
  return d_state_type->tm().mk_and(assumption_terms);
}

trace_helper* transition_system::get_trace_helper() const {
  return d_trace_helper;
}

transition_system::~transition_system() {
  for (size_t i = 0; i < d_assumptions.size(); ++ i) {
    delete d_assumptions[i];
  }
  for (size_t i = 0; i < d_invariants.size(); ++ i) {
    delete d_invariants[i];
  }
  delete d_initial_states;
  delete d_transition_relation;
  delete d_trace_helper;
}

}
}
