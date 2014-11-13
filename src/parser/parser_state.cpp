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

  expr::state_type type(id);

  for(size_t i = 0; i < vars.size(); ++ i) {
    type.add_variable(vars[i], types[i]);
  }

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
  if (d_types.has_entry(id)) {
    return d_types.get_entry(id);
  } else {
    report_error("unknown type: " + id);
    return expr::term_ref();
  }
}
