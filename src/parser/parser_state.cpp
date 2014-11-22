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

parser_state::parser_state(system::context& context)
: d_context(context)
, d_variables_local("local vars")
, d_types("types")
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.realType()));
  d_types.add_entry("Boolean", term_ref_strong(tm, tm.booleanType()));
  d_types.add_entry("Integer", term_ref_strong(tm, tm.integerType()));
}

string parser_state::token_text(pANTLR3_COMMON_TOKEN token) const {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref parser_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref parser_state::get_variable(std::string id) const {
  if (!d_variables_local.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables_local.get_entry(id);
}

void parser_state::expand_vars(term_ref var_ref) {

  // The variable content
  const term& var_term = tm().term_of(var_ref);

  /// Variable name
  std::string var_name = tm().get_variable_name(var_term);

  // Number of subfields
  size_t size = tm().get_struct_size(var_term);

  if (size == 0) {
    // Atomic, just put into the symbol table
    d_variables_local.add_entry(var_name, var_ref);
  } else {
    // Register all the field variables
    for (size_t i = 0; i < size; ++ i) {
      // Get the field
      term_ref var_field_ref = tm().get_struct_field(var_term, i);
      // Expand
      expand_vars(var_field_ref);
    }
  }
}

void parser_state::use_state_type(std::string id, state_type::var_class var_class, bool use_namespace) {
  const system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void parser_state::use_state_type(const system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

  // Use the appropriate namespace
  st->use_namespace(tm());
  if (use_namespace) {
    st->use_namespace(tm(), var_class);
  }

  // Get the state
  term_ref state_var_ref = st->get_state(var_class);

  // Declare the variables
  expand_vars(state_var_ref);

  // Pop the namespace
  tm().pop_namespace();
}

void parser_state::push_scope() {
  d_variables_local.push_scope();
}

void parser_state::pop_scope() {
  d_variables_local.pop_scope();
}

void parser_state::ensure_declared(std::string id, parser_object type, bool declared) {
  bool ok = declared;
  switch (type) {
  case PARSER_VARIABLE:
    ok = d_variables_local.has_entry(id);
    break;
  case PARSER_TYPE:
    ok = d_variables_local.has_entry(id);
    break;
  case PARSER_STATE_TYPE:
    ok = d_context.has_state_type(id);
    break;
  case PARSER_STATE_FORMULA:
    ok = d_context.has_state_formula(id);
    break;
  case PARSER_TRANSITION_FORMULA:
    ok = d_context.has_transition_formula(id);
    break;
  case PARSER_TRANSITION_SYSTEM:
    ok = d_context.has_transition_system(id);
    break;
  case PARSER_OBJECT_LAST:
    // Always noop
    return;
  default:
    assert(false);
  }

  if (ok != declared) {
    if (declared) throw parser_exception(id + " not declared");
    else throw parser_exception(id + " already declared");
  }
}
