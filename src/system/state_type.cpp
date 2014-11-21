/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "system/state_type.h"

#include "expr/term_manager.h"

using namespace sal2;
using namespace state;
using namespace expr;

state_type::state_type(term_manager& tm, std::string id, term_ref type)
: d_id(id)
, d_type(tm, type)
{
  d_current_state = term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(CURRENT), type));
  d_next_state = term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(NEXT), type));
}

void state_type::use_namespace(term_manager& tm) const {
  tm.use_namespace(d_id + "::");
}

void state_type::use_namespace(term_manager& tm, var_class vc) const {
  tm.use_namespace(to_string(vc) + ".");
}

void state_type::to_stream(std::ostream& out) const {
  out << "[" << d_id << ": " << d_type << "]";
}

term_ref state_type::get_state(var_class vc) const {
  switch (vc) {
  case CURRENT:
    return d_current_state;
  case NEXT:
    return d_next_state;
  }
  assert(false);
  return term_ref();
}

std::string state_type::to_string(var_class vc) {
  switch (vc) {
  case CURRENT:
    return "state";
  case NEXT:
    return "next";
  }
  assert(false);
  return "unknown";
}

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << ": " << d_state_formula << "]";
}

void state_transition_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_transition_formula << "]";
}

void state_transition_system::to_stream(std::ostream& out) const {
  out << "[" << std::endl;
  out << "type: " << d_state_type << std::endl;
  out << "I: " << d_initial_states.get_formula() << std::endl;
  out << "T: [" << std::endl;
  for (size_t i = 0; i < d_transition_relation.size(); ++ i) {
    out << "\t" << d_transition_relation[i].get_formula() << std::endl;
  }
  out << "]]";
}

