/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include <iostream>

#include "system/state_type.h"
#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include <iostream>

namespace sally {
namespace system {

state_type::state_type(std::string id, expr::term_manager& tm, expr::term_ref type)
: gc_participant(tm)
, d_id(id)
, d_tm(tm)
, d_type(tm, type)
{
  // Create the state variables
  d_current_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_CURRENT), type));
  d_next_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_NEXT), type));

  // Get the variables
  d_tm.get_variables(d_current_state, d_current_vars);
  d_tm.get_variables(d_next_state, d_next_vars);

  // Remove the first one (the struct variable)
  for (size_t i = 0; i + 1 < d_current_vars.size(); ++ i) {
    d_current_vars[i] = d_current_vars[i+1];
    d_next_vars[i] = d_next_vars[i+1];
  }
  d_current_vars.pop_back();
  d_next_vars.pop_back();

  // Make the substitution map
  for (size_t i = 0; i < d_current_vars.size(); ++ i) {
    d_subst_current_next[d_current_vars[i]] = d_next_vars[i];
    d_subst_next_current[d_next_vars[i]] = d_current_vars[i];
  }
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

expr::term_ref state_type::get_state_type_variable(var_class vc) const {
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

const std::vector<expr::term_ref>& state_type::get_variables(var_class vc) const {
  switch (vc) {
  case STATE_CURRENT:
    return d_current_vars;
  case STATE_NEXT:
    return d_next_vars;
  default:
    assert(false);
    return d_current_vars;
  }
}

bool state_type::is_state_formula(expr::term_ref f) const {
  // State variables
  std::set<expr::term_ref> state_variables;
  d_tm.get_variables(get_state_type_variable(STATE_CURRENT), state_variables);
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(state_variables.begin(), state_variables.end(), f_variables.begin(), f_variables.end());
}

bool state_type::is_transition_formula(expr::term_ref f) const {
  // State and next variables
  std::set<expr::term_ref> state_variables;
  d_tm.get_variables(get_state_type_variable(STATE_CURRENT), state_variables);
  d_tm.get_variables(get_state_type_variable(STATE_NEXT), state_variables);
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(state_variables.begin(), state_variables.end(), f_variables.begin(), f_variables.end());
}

expr::term_ref state_type::change_formula_vars(var_class from, var_class to, expr::term_ref f) const {
  if (from == to) {
    return f;
  }
  if (from == STATE_CURRENT && to == STATE_NEXT) {
    return tm().substitute(f, d_subst_current_next);
  }
  if (from == STATE_NEXT && to == STATE_CURRENT) {
    return tm().substitute(f, d_subst_next_current);
  }
  // They are the same
  return f;
}

std::string state_type::get_canonical_name(std::string id, var_class vc) const {
  // The name
  std::string canonical = d_id + "::" + to_string(vc) + "." + id;
  // Reduce using the term manager rules
  canonical = d_tm.name_normalize(canonical);
  // Return the name
  return canonical;
}

void state_type::gc_collect(const expr::gc_info& gc_reloc) {
  size_t ret;

  gc_reloc.collect(d_type);
  gc_reloc.collect(d_current_state);
  gc_reloc.collect(d_next_state);
  ret = gc_reloc.collect(d_current_vars.begin(), d_current_vars.end());
  assert(ret == 0);
  ret = gc_reloc.collect(d_next_vars.begin(), d_next_vars.end());
  assert(ret == 0);
  gc_reloc.collect(d_subst_current_next);
  gc_reloc.collect(d_subst_next_current);
}

}
}
