/*
 * transition_system.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/transition_system.h"

#include <iostream>

namespace sally {
namespace system {

void transition_system::to_stream(std::ostream& out) const {
  out << "[" << std::endl;
  out << "type: " << *d_state_type << std::endl;
  out << "I: " << d_initial_states->get_formula() << std::endl;
  out << "T: [" << std::endl;
  for (size_t i = 0; i < d_transition_relation.size(); ++ i) {
    out << "\t" << d_transition_relation[i]->get_formula() << std::endl;
  }
  out << "]]";
}

std::ostream& operator << (std::ostream& out, const transition_system& T) {
  T.to_stream(out);
  return out;
}

expr::term_ref transition_system::get_transition_relation() const {
  std::vector<expr::term_ref> transitions;
  for (size_t i = 0; i < d_transition_relation.size(); ++ i) {
    transitions.push_back(d_transition_relation[i]->get_formula());
  }
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

expr::term_ref transition_system::get_assumption() const {
  std::vector<expr::term_ref> assumption_terms;
  for (size_t i = 0; i < d_assumptions.size(); ++ i) {
    assumption_terms.push_back(d_assumptions[i]->get_formula());
  }
  return d_state_type->tm().mk_and(assumption_terms);
}


transition_system::~transition_system() {
  for (size_t i = 0; i < d_assumptions.size(); ++ i) {
    delete d_assumptions[i];
  }
}


}
}
