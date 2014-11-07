/*
 * parser_state.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/state.h"

#include "utils/symbol_table.h"

namespace sal2 {

namespace parser {

/** State attached to the parser */
class parser_state {

  /** The term manager */
  expr::term_manager& d_term_manager;

  /** Symbol table for state types */
  utils::symbol_table<expr::state_type> d_state_types;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref> d_types;

public:

  parser_state(expr::term_manager& tm);

  expr::term_manager& tm() {
    return d_term_manager;
  }

  /** Report an error */
  void report_error(std::string msg);

  /** Declare a new state type */
  void declare_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types);
};

}
}
