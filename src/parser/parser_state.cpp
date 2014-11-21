/*
 * parser_state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "parser/parser_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"

#include <cassert>

using namespace sal2;
using namespace parser;
using namespace expr;
using namespace system;

using namespace std;

parser_state::parser_state(term_manager& tm)
: d_term_manager(tm)
, d_state_types("state types")
, d_state_formulas("state formulas")
, d_transition_formulas("state transition formulas")
, d_transition_systems("state transition systems")
, d_variables_local("local vars")
, d_types("types")
{
  // Add the basic types
  d_types.add_entry("Real", term_ref_strong(tm, tm.realType()));
  d_types.add_entry("Boolean", term_ref_strong(tm, tm.booleanType()));
  d_types.add_entry("Integer", term_ref_strong(tm, tm.integerType()));
}

void parser_state::report_error(string msg) const {
  throw parser_exception(msg);
}

string parser_state::token_text(pANTLR3_COMMON_TOKEN token) const {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref parser_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    report_error("undeclared type: " + id);
    return term_ref();
  }
  return d_types.get_entry(id);
}

term_ref parser_state::get_variable(std::string id) const {
  if (!d_variables_local.has_entry(id)) {
    report_error("undeclared variable: " + id);
    return term_ref();
  }
  return d_variables_local.get_entry(id);
}

const state_type& parser_state::new_state_type(string id, const vector<string>& vars, const vector<term_ref>& types) {
  assert(vars.size() == types.size());
  assert(vars.size() > 0);

  if (d_state_types.has_entry(id)) {
    throw parser_exception(id + " already declared");
  }

  // Create the type
  term_ref type = d_term_manager.mk_struct(vars, types);

  // Add the mapping id -> type
  return d_state_types.add_entry(id, state_type(d_term_manager, id, type));
}

const state_type& parser_state::get_state_type(string id) const {
  if (!d_state_types.has_entry(id)) {
    throw parser_exception("undeclared state type: " + id);
  }
  return d_state_types.get_entry(id);
}

void parser_state::expand_vars(term_ref var_ref) {

  // The variable content
  const term& var_term = d_term_manager.term_of(var_ref);

  /// Variable name
  std::string var_name = d_term_manager.get_variable_name(var_term);

  // Number of subfields
  size_t size = d_term_manager.get_struct_size(var_term);

  if (size == 0) {
    // Atomic, just put into the symbol table
    d_variables_local.add_entry(var_name, var_ref);
  } else {
    // Register all the field variables
    for (size_t i = 0; i < size; ++ i) {
      // Get the field
      term_ref var_field_ref = d_term_manager.get_struct_field(var_term, i);
      // Expand
      expand_vars(var_field_ref);
    }
  }
}

void parser_state::use_state_type(std::string id, state_type::var_class var_class, bool use_namespace) {
  const state_type& st = get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void parser_state::use_state_type(const state_type& st , state_type::var_class var_class, bool use_namespace) {

  // Use the appropriate namespace
  st.use_namespace(d_term_manager);
  if (use_namespace) {
    st.use_namespace(d_term_manager, var_class);
  }

  /** Get the state */
  term_ref state_var_ref = st.get_state(var_class);

  /** Declare the variable */
  expand_vars(state_var_ref);

  // Pop the namespace
  d_term_manager.pop_namespace();
}

const state_formula& parser_state::new_state_formula(std::string id, std::string type_id, term_ref f) {
  // Get the information about the state types
  const state_type& state_type = get_state_type(type_id);
  // Add to the symbol table
  return d_state_formulas.add_entry(id, state_formula(d_term_manager, state_type, f));
}

const state_formula& parser_state::get_state_formula(string id) const {
  if (!d_state_formulas.has_entry(id)) {
    throw parser_exception("undeclared state set: " + id);
  }
  return d_state_formulas.get_entry(id);
}

const transition_formula& parser_state::new_transition_formula(std::string id, std::string type_id, term_ref f) {

  if (d_transition_formulas.has_entry(id)) {
    report_error(id + " already declared");
  }

  // Get the information about the state types
  const state_type& state_type = get_state_type(type_id);

  // Add to the symbol table
  return d_transition_formulas.add_entry(id, transition_formula(d_term_manager, state_type, f));
}

const transition_formula& parser_state::get_transition_formula(string id) const {
  if (!d_transition_formulas.has_entry(id)) {
    throw parser_exception("undeclared transition: " + id);
  }
  return d_transition_formulas.get_entry(id);
}

const transition_system& parser_state::new_transition_system(std::string id, std::string type_id, std::string initial_id, std::vector<std::string>& transitions) {

  if (d_transition_systems.has_entry(id)) {
    report_error(id + " already declared");
  }

  // Get the information about the state types
  const state_type& state_type = get_state_type(type_id);

  // Get the initial states
  const state_formula& initial_states = get_state_formula(initial_id);

  // Get the transition relations
  std::vector<transition_formula> transition_formulas;
  for (size_t i = 0; i < transitions.size(); ++ i) {
    // Create the state formula
    transition_formulas.push_back(get_transition_formula(transitions[i]));
  }

  // Put it into the symbol table
  return d_transition_systems.add_entry(id, transition_system(state_type, initial_states, transition_formulas));
}

const transition_system& parser_state::get_transition_system(string id) const {
  if (!d_transition_systems.has_entry(id)) {
    throw parser_exception("undeclared transition system: " + id);
  }
  return d_transition_systems.get_entry(id);
}

void parser_state::push_scope() {
  d_variables_local.push_scope();
}

void parser_state::pop_scope() {
  d_variables_local.pop_scope();
}

