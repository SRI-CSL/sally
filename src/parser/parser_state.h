/*
 * parser_state.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"

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

  /** Construct the parser state */
  parser_state(expr::term_manager& tm);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() { return d_term_manager; }

  /** Report an error */
  void report_error(std::string msg) const;

  /** Create a command to declare a new state type */
  command* declare_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types);

  /** Create a command to define a set of states given by the formula */
  command* define_states(std::string id, std::string type_id, expr::term_ref sf);

  /** Returns the variables assoicated with the given state */
  void get_state_variables(std::string id, expr::state::var_class vc, std::vector<expr::term_ref>& vars) const;

  /** Use the state type, i.e. declare the variables prefix.x, prefix.y, ... */
  void use_state_type(std::string id, expr::state::var_class var_class);

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
