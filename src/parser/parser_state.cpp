/*
 * parser_state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "parser/parser_state.h"

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

}


void parser_state::declare_state_type(string id, const vector<string>& vars, const vector<term_ref>& types) {
  assert(vars.size() == types.size());
  assert(vars.size() > 0);

  expr::state_type result(id);

  for(size_t i = 0; i < vars.size(); ++ i) {
    result.add_variable(vars[i], types[i]);
  }

}
