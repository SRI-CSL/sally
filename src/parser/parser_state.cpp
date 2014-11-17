/*
 * parser_state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "parser/parser_state.h"
#include "parser/parser.h"

#include <cassert>

using namespace sal2;
using namespace parser;
using namespace expr;

using namespace std;

parser_state::parser_state(term_manager& tm)
: d_term_manager(tm)
, d_state_types("state types")
, d_variables_local("local vars")
, d_variables_global("global vars")
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


command* parser_state::declare_state_type(string id, const vector<string>& vars, const vector<term_ref>& types) {
  assert(vars.size() == types.size());
  assert(vars.size() > 0);

  size_t n = vars.size();

  // Create the variable names
  vector<term_ref> type_argumens;
  for (size_t i = 0; i < n; ++ i) {
    type_argumens.push_back(d_term_manager.mk_term<CONST_STRING>(vars[i]));
    type_argumens.push_back(types[i]);
  }

  // Make the struct type
  term_ref type = d_term_manager.mk_term<TYPE_STRUCT>(type_argumens.begin(), type_argumens.end());

  // Add the mapping id -> type
  d_state_types.add_entry(id, term_ref_strong(d_term_manager, type));

  return new declare_state_type_command(type);
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

void parser_state::use_state_type(std::string id, std::string prefix) {

  if (!d_state_types.has_entry(id)) {
    report_error("unknown state type: " + id);
  }

  // Mark a new scope
  d_variables_local.new_scope();

  // Get the types information
  expr::term_ref state_type_ref = d_state_types.get_entry(id);
  const expr::term& state_type = d_term_manager.term_of(state_type_ref);

  for (size_t i = 0; i < state_type.size(); i += 2) {
    // Get the variable id
    std::string var_id = d_term_manager.payload_of<std::string>(state_type[i]);
    expr::term_ref var_type = state_type[i+1];

    // Create the complete name
    std::string var_local_name = prefix + "." + var_id;
    std::string var_global_name = id + "::" + prefix + "." + var_id;

    // Not there before, add it
    if (!d_variables_global.has_entry(var_global_name)) {
      // Create it
      expr::term_ref var = d_term_manager.mk_term<VARIABLE>(var_global_name, var_type);
      d_variables_global.add_entry(var_global_name, expr::term_ref_strong(d_term_manager, var));
    }

    // Get the unique var for this prefix
    expr::term_ref var = d_variables_global.get_entry(var_global_name);

    // Add to local scope
    d_variables_local.add_entry(var_local_name, var);
  }
}

void parser_state::pop_local() {
  // Pop the local scope
  d_variables_local.pop_scope();
}
