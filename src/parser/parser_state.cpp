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
, d_variables("local vars")
, d_types("types")
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.realType()));
  d_types.add_entry("Boolean", term_ref_strong(tm, tm.booleanType()));
  d_types.add_entry("Integer", term_ref_strong(tm, tm.integerType()));
}

string parser_state::token_text(pANTLR3_COMMON_TOKEN token) {
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
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

void parser_state::use_state_type(std::string id, state_type::var_class var_class, bool use_namespace) {
  const system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void parser_state::use_state_type(const system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

  // Use the appropriate namespace
  st->use_namespace();
  if (use_namespace) {
    st->use_namespace(var_class);
  }

  // Declare the variables
  std::vector<expr::term_ref> vars;
  st->get_variables(var_class, vars);
  for (size_t i = 0; i < vars.size(); ++ i) {
    const term& var_term = tm().term_of(vars[i]);
    std::string var_name = tm().get_variable_name(var_term);
    d_variables.add_entry(var_name, vars[i]);
  }

  // Pop the namespace
  tm().pop_namespace();
  if (use_namespace) {
    tm().pop_namespace();
  }
}

void parser_state::push_scope() {
  d_variables.push_scope();
}

void parser_state::pop_scope() {
  d_variables.pop_scope();
}

void parser_state::ensure_declared(std::string id, parser_object type, bool declared) {
  bool ok = declared;
  switch (type) {
  case PARSER_VARIABLE:
    ok = d_variables.has_entry(id);
    break;
  case PARSER_TYPE:
    ok = d_types.has_entry(id);
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
