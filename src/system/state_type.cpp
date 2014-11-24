/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include <iostream>

#include "system/state_type.h"
#include "expr/term_manager.h"

#include <iostream>

namespace sal2 {
namespace system {

state_type::state_type(expr::term_manager& tm, std::string id, expr::term_ref type)
: d_tm(tm)
, d_id(id)
, d_type(tm, type)
{
  d_current_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_CURRENT), type));
  d_next_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_NEXT), type));
}

void state_type::use_namespace() const {
  d_tm.use_namespace(d_id + "::");
}

void state_type::use_namespace(var_class vc) const {
  d_tm.use_namespace(to_string(vc) + ".");
}

void state_type::to_stream(std::ostream& out) const {
  out << "[" << d_id << ": " << d_type << "]";
}

expr::term_ref state_type::get_state(var_class vc) const {
  switch (vc) {
  case STATE_CURRENT:
    return d_current_state;
  case STATE_NEXT:
    return d_next_state;
  }
  assert(false);
  return expr::term_ref();
}

std::string state_type::to_string(var_class vc) {
  switch (vc) {
  case STATE_CURRENT:
    return "state";
  case STATE_NEXT:
    return "next";
  }
  assert(false);
  return "unknown";
}

std::ostream& operator << (std::ostream& out, const state_type& st) {
  st.to_stream(out);
  return out;
}

void state_type::get_variables(var_class vc, std::vector<expr::term_ref>& out) const {
  d_tm.get_variables(get_state(vc), out);
}

bool state_type::is_state_formula(expr::term_ref f) const {
  // State variables
  std::set<expr::term_ref> state_variables;
  d_tm.get_variables(get_state(STATE_CURRENT), state_variables);
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(state_variables.begin(), state_variables.end(), f_variables.begin(), f_variables.end());
}

bool state_type::is_transition_formula(expr::term_ref f) const {
  // State and next variables
  std::set<expr::term_ref> state_variables;
  d_tm.get_variables(get_state(STATE_CURRENT), state_variables);
  d_tm.get_variables(get_state(STATE_NEXT), state_variables);
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(state_variables.begin(), state_variables.end(), f_variables.begin(), f_variables.end());
}

expr::term_ref state_type::unroll(expr::term_ref transition_f, size_t n) const {
  expr::term_ref f = transition_f;
  return f;
}

}
}
