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

#include <iostream>

#include "system/state_type.h"
#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include <iostream>

namespace sally {
namespace system {

state_type::state_type(std::string id, expr::term_manager& tm, expr::term_ref state_type_var, expr::term_ref input_type_var)
: gc_participant(tm)
, d_id(id)
, d_tm(tm)
, d_state_type_var(tm, state_type_var)
, d_input_type_var(tm, input_type_var)
{
  // Create the state variables
  d_current_vars_struct = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_CURRENT), state_type_var));
  d_input_vars_struct = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_INPUT), input_type_var));
  d_next_vars_struct = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(STATE_NEXT), state_type_var));

  // Get the variables
  d_tm.get_struct_fields(d_tm.term_of(d_current_vars_struct), d_current_vars);
  d_tm.get_struct_fields(d_tm.term_of(d_input_vars_struct), d_input_vars);
  d_tm.get_struct_fields(d_tm.term_of(d_next_vars_struct), d_next_vars);

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
  out << "[" << d_id << ": " << d_state_type_var << " : " << d_input_type_var << "]";
}

expr::term_ref state_type::get_vars_struct(var_class vc) const {
  switch (vc) {
  case STATE_CURRENT:
    return d_current_vars_struct;
  case STATE_INPUT:
    return d_input_vars_struct;
  case STATE_NEXT:
    return d_next_vars_struct;
  }
  assert(false);
  return expr::term_ref();
}

std::string state_type::to_string(var_class vc) {
  switch (vc) {
  case STATE_CURRENT:
    return "state";
  case STATE_INPUT:
    return "input";
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
  case STATE_INPUT:
    return d_input_vars;
  case STATE_NEXT:
    return d_next_vars;
  default:
    assert(false);
    return d_current_vars;
  }
}

bool state_type::is_state_formula(expr::term_ref f) const {
  // State variables
  std::set<expr::term_ref> state_variables(d_current_vars.begin(), d_current_vars.end());
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(state_variables.begin(), state_variables.end(), f_variables.begin(), f_variables.end());
}

bool state_type::is_transition_formula(expr::term_ref f) const {
  // State and next variables
  std::set<expr::term_ref> all_variables;
  all_variables.insert(d_current_vars.begin(), d_current_vars.end());
  all_variables.insert(d_input_vars.begin(), d_input_vars.end());
  all_variables.insert(d_next_vars.begin(), d_next_vars.end());
  // Formula variables
  std::set<expr::term_ref> f_variables;
  d_tm.get_variables(f, f_variables);
  // State formula if only over state variables
  return std::includes(all_variables.begin(), all_variables.end(), f_variables.begin(), f_variables.end());
}

expr::term_ref state_type::change_formula_vars(var_class from, var_class to, expr::term_ref f) const {
  assert(from != STATE_INPUT && to != STATE_INPUT);
  if (from == to) {
    return f;
  }
  if (from == STATE_CURRENT && to == STATE_NEXT) {
    return tm().substitute_and_cache(f, const_cast<state_type*>(this)->d_subst_current_next);
  }
  if (from == STATE_NEXT && to == STATE_CURRENT) {
    return tm().substitute_and_cache(f, const_cast<state_type*>(this)->d_subst_next_current);
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

void state_type::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_state_type_var);
  gc_reloc.reloc(d_input_type_var);
  gc_reloc.reloc(d_current_vars_struct);
  gc_reloc.reloc(d_input_vars_struct);
  gc_reloc.reloc(d_next_vars_struct);
  gc_reloc.reloc(d_current_vars);
  gc_reloc.reloc(d_input_vars);
  gc_reloc.reloc(d_next_vars);
  gc_reloc.reloc(d_subst_current_next);
  gc_reloc.reloc(d_subst_next_current);
}

}
}
