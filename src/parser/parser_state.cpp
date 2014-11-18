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

enum state_var_class {
  STATE_CURRENT,
  STATE_NEXT
};

command* parser_state::declare_state_type(string id, const vector<string>& vars, const vector<term_ref>& types) {
  assert(vars.size() == types.size());
  assert(vars.size() > 0);

  if (d_state_types.has_entry(id)) {
    throw parser_exception("state type " + id + " already declared");
  }

  // Create the type
  term_ref type = d_term_manager.mk_struct(vars, types);

  // Add the mapping id -> type
  d_state_types.add_entry(id, term_ref_strong(d_term_manager, type));

  std::string var_name;
  expr::term_ref var;
  for (size_t i = 0; i < vars.size(); ++ i) {

    // Current state variables
    var_name = expr::state::get_var_name(id, vars[i], expr::state::CURRENT, true);
    var = d_term_manager.mk_variable(var_name, types[i]);
    if (d_variables_global.has_entry(var_name)) {
      throw parser_exception("variable " + var_name + " already declared");
    } else {
      d_variables_global.add_entry(var_name, expr::term_ref_strong(d_term_manager, var));
    }

    // Next state variables
    var_name = expr::state::get_var_name(id, vars[i], expr::state::NEXT, true);
    var = d_term_manager.mk_variable(var_name, types[i]);
    if (d_variables_global.has_entry(var_name)) {
      throw parser_exception("variable " + var_name + " already declared");
    } else {
      d_variables_global.add_entry(var_name, expr::term_ref_strong(d_term_manager, var));
    }

  }

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

void parser_state::get_state_variables(std::string id, expr::state::var_class var_class, std::vector<expr::term_ref>& vars) const {
  assert(d_state_types.has_entry(id));

  // Get the information about the state types
  expr::term_ref state_type_ref = d_state_types.get_entry(id);
  const expr::term& state_type = d_term_manager.term_of(state_type_ref);

  for (size_t i = 0; i < d_term_manager.get_struct_size(state_type); i ++) {
    // Get the id of the struct element
    std::string var_id = d_term_manager.get_struct_element_id(state_type, i);
    // Create the complete name
    std::string var_global_name = state::get_var_name(id, var_id, var_class, true);
    // Add variable to the output
    vars.push_back(d_variables_global.get_entry(var_global_name));
  }

}

void parser_state::use_state_type(std::string id, expr::state::var_class var_class) {

  if (!d_state_types.has_entry(id)) {
    report_error("unknown state type: " + id);
  }

  // Mark a new scope
  d_variables_local.new_scope();

  // Get the information about the state types
  expr::term_ref state_type_ref = d_state_types.get_entry(id);
  const expr::term& state_type = d_term_manager.term_of(state_type_ref);

  for (size_t i = 0; i < d_term_manager.get_struct_size(state_type); i ++) {
    // Get the id of the struct element
    std::string var_id = d_term_manager.get_struct_element_id(state_type, i);
    // Create the complete name
    std::string var_global_name = state::get_var_name(id, var_id, var_class, true);
    // Create the local name
    std::string var_local_name = state::get_var_name(id, var_id, var_class, false);
    // Get the actual variable
    term_ref var = d_variables_global.get_entry(var_global_name);
    // Add to local scope
    d_variables_local.add_entry(var_local_name, var);
  }

}

command* parser_state::define_states(std::string id, std::string type_id, expr::term_ref sf) {

  if (!d_state_types.has_entry(id)) {
    report_error("unknown state type: " + id);
  }

  // Get the information about the state types
  expr::term_ref state_type_ref = d_state_types.get_entry(id);
  const expr::term& state_type = d_term_manager.term_of(state_type_ref);

  for (size_t i = 0; i < d_term_manager.get_struct_size(state_type); i ++) {
    // Get the id of the struct element
    std::string var_id = d_term_manager.get_struct_element_id(state_type, i);
    // Create the complete name
    std::string var_global_name = state::get_var_name(id, var_id, var_class, true);
    // Create the local name
    std::string var_local_name = state::get_var_name(id, var_id, var_class, false);
    // Get the actual variable
    term_ref var = d_variables_global.get_entry(var_global_name);
    // Add to local scope
    d_variables_local.add_entry(var_local_name, var);
  }

}


void parser_state::pop_local() {
  // Pop the local scope
  d_variables_local.pop_scope();
}
