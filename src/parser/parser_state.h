/*
 * parser_state.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/state.h"

#include "parser/command.h"
#include "utils/symbol_table.h"

#include <antlr3.h>

namespace sal2 {

namespace parser {

/** State attached to the parser */
class parser_state {

  /** The term manager */
  expr::term_manager& d_term_manager;

  /** Symbol table for state types */
  utils::symbol_table<expr::term_ref_strong> d_state_types;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables_local;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref_strong> d_variables_global;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

public:

  parser_state(expr::term_manager& tm);

  expr::term_manager& tm() {
    return d_term_manager;
  }

  /** Report an error */
  void report_error(std::string msg) const;

  /** Declare a new state type */
  command* declare_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types);

  /** Use the state type, i.e. declare the variables prefix.x, prefix.y, ... */
  void use_state_type(std::string id, std::string prefix);

  /** Pop the locate declarations */
  void pop_local();

  /** Returns the type with the given id */
  expr::term_ref get_type(std::string id) const;

  /** Returns the a variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Get the string of a token begin parsed */
  std::string token_text(pANTLR3_COMMON_TOKEN token) const;
};

}
}
