/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "expr/state.h"

using namespace sal2;
using namespace expr;

void state_type::add_variable(const term_ref_strong& variable) {
}


void state_type::to_stream(std::ostream& out) const {
  out << "[" << d_name << ":";
  std::map<std::string, term_ref>::const_iterator it;
  for (it = d_var_to_type_map.begin(); it != d_var_to_type_map.end(); ++ it) {
    out << " (" << it->first << " " << it->second << ")";
  }
}

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_formula << "]";
}

void state_transition_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_transition_formula << "]";
}

