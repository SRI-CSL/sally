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
{
  // Add the basic types
  d_types.add_entry("Real", tm.realType());
  d_types.add_entry("Boolean", tm.booleanType());
  d_types.add_entry("Integer", tm.integerType());
}

void parser_state::report_error(string msg) {
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

  // TODO: sort the arrays
  term_ref type = d_term_manager.mk_term<TYPE_STRUCT>(type_argumens.begin(), type_argumens.end());

  cout << "Adding state type: " << type << endl;
  d_state_types.add_entry(id, type);

  return new declare_state_type_command(type);
}

string parser_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

expr::term_ref parser_state::get_type(std::string id) {
  if (!d_types.has_entry(id)) {
    report_error("undeclared type: " + id);
    return expr::term_ref();
  }
  return d_types.get_entry(id);
}

expr::term_ref parser_state::get_variable(std::string id) {
  if (!d_variables.has_entry(id)) {
    report_error("undeclared variable: " + id);
    return expr::term_ref();
  }
  return d_variables.get_entry(id);
}

void parser_state::use_state_type(std::string id) {
  if (!d_state_types.has_entry(id)) {
    report_error("unknown state type: " + id);
  }

  expr::term_ref state_type_ref = d_state_types.get_entry(id);
  const expr::term& state_type = d_term_manager.term_of(state_type_ref);

  for (size_t i = 0; i < state_type.size(); ++ i) {
    std::string id = state_type.
  }

}
