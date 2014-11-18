/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "expr/state.h"
#include "expr/term_manager.h"

using namespace sal2;
using namespace expr;

void state_formula::to_stream(std::ostream& out) const {
  out << "[(";
  for (size_t i = 0; i < d_state_variables.size(); ++ i) {
    if (i) { out << " "; }
    out << "(" << d_state_variables[i] << ", " << d_tm.get_variable_type(d_tm.term_of(d_state_variables[i])) << ")";
  }
  out << ")";
  out << d_state_formula;
  out << "]";
}

void state_transition_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_transition_formula << "]";
}

std::string state::get_var_name(std::string state_type_id, std::string var_name, var_class vc, bool full) {

  std::string prefix;
  switch (vc) {
  case CURRENT: prefix = "state"; break;
  case NEXT: prefix = "next"; break;
  }

  if (full) {
    return state_type_id + "::" + prefix + "." + var_name;
  } else {
    return prefix + "." + var_name;
  }

}
