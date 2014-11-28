/*
 * transition_system.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/transition_system.h"

#include <iostream>

namespace sal2 {
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
  if (d_transition_relation.size() == 0) {
    return d_state_type->tm().mk_boolean_constant(false);
  }
  std::vector<expr::term_ref> transitions;
  for (size_t i = 0; i < d_transition_relation.size(); ++ i) {
    transitions.push_back(d_transition_relation[i]->get_formula());
  }
  if (transitions.size() == 1) {
    return transitions[0];
  } else {
    return d_state_type->tm().mk_term(expr::TERM_OR, transitions);
  }
}

}
}
