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

using namespace std;

parser_state::parser_state(term_manager& tm)
: d_term_manager(tm)
, d_state_types("state types")
, d_state_formulas("state formulas")
, d_transition_formulas("state transition formulas")
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

expr::term_ref parser_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    report_error("undeclared type: " + id);
    return expr::term_ref();
  }
  return d_types.get_entry(id);
}

expr::term_ref parser_state::get_variable(std::string id) const {
  if (!d_variables_local.has_entry(id)) {
    report_error("undeclared variable: " + id);
    return expr::term_ref();
  }
  return d_variables_local.get_entry(id);
}

expr::state_type parser_state::new_state_type(string id, const vector<string>& vars, const vector<term_ref>& types) {
  assert(vars.size() == types.size());
  assert(vars.size() > 0);

  if (d_state_types.has_entry(id)) {
    throw parser_exception("state type " + id + " already declared");
  }

  // Create the type
  term_ref type = d_term_manager.mk_struct(vars, types);

  // Create the state type
  expr::state_type state_type(d_term_manager, id, type);

  // Add the mapping id -> type
  d_state_types.add_entry(id, state_type);

  // Return the command
  return state_type;
}

void parser_state::expand_vars(expr::term_ref var_ref) {

  // The variable content
  const term& var_term = d_term_manager.term_of(var_ref);

  /// Variable name
  std::string var_name = d_term_manager.get_variable_name(var_term);

  // Number of subfields
  size_t size = d_term_manager.get_struct_size(var_term);

  if (size == 0) {

    std::cerr << "Declaring variable " << var_ref << " as " << var_name << std::endl;

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

void parser_state::use_state_type(std::string id, expr::state_type::var_class var_class, bool use_namespace) {

  if (!d_state_types.has_entry(id)) {
    report_error("unknown state type: " + id);
  }

  // Get the information about the state types
  const expr::state_type& st = d_state_types.get_entry(id);

  // Use the apropriate namespace
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

expr::state_formula parser_state::new_state_formula(std::string id, std::string type_id, expr::term_ref f) {

  if (!d_state_types.has_entry(type_id)) {
    report_error("unknown state type: " + id);
  }

  // Get the information about the state types
  const expr::state_type& state_type = d_state_types.get_entry(type_id);

  // Create the state formula
  expr::state_formula sf(d_term_manager, state_type, f);

  // Add to the symbol table
  d_state_formulas.add_entry(id, sf);

  /** Return thecommand */
  return sf;
}

expr::state_transition_formula parser_state::new_state_transition_formula(std::string id, std::string type_id, expr::term_ref f) {

  if (!d_state_types.has_entry(type_id)) {
    report_error("unknown state type: " + id);
  }

  // Get the information about the state types
  const expr::state_type& state_type = d_state_types.get_entry(type_id);

  // Create the state formula
  expr::state_transition_formula tf(d_term_manager, state_type, f);

  // Add to the symbol table
  d_transition_formulas.add_entry(id, tf);

  /** Return thecommand */
  return tf;
}


void parser_state::push_scope() {
  d_variables_local.push_scope();
}

void parser_state::pop_scope() {
  d_variables_local.pop_scope();
}

