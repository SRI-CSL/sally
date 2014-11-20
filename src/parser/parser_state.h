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
  utils::symbol_table<expr::state_type> d_state_types;

  /** Symbol table for state formulas */
  utils::symbol_table<expr::state_formula> d_state_formulas;

  /** Symbol table for state transition formulas */
  utils::symbol_table<expr::state_transition_formula> d_transition_formulas;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables_local;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

  /**
   * Declare the variables from the (possibly struct) variable var into the
   * variables symbol table.
   */
  void expand_vars(std::string name, expr::term_ref var);

public:

  /** Construct the parser state */
  parser_state(expr::term_manager& tm);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() { return d_term_manager; }

  /** Report an error */
  void report_error(std::string msg) const;

  /** Create a command to declare a new state type */
  command* declare_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types);

  /** Create a command to define a set of states id given by the formula */
  command* define_states(std::string id, std::string type_id, expr::term_ref sf);

  /** Create a command to define a transition formula id for given state types*/
  command* define_transition(std::string id, std::string type_id, expr::term_ref stf);

  /** Use the state type, i.e. declare the variables prefix.x, prefix.y, ... */
  void use_state_type(std::string id, expr::state_type::var_class var_class);

  /** Push a new scope for local declarations */
  void push_scope();

  /** Pop the locate declarations */
  void pop_scope();

  /** Returns the type with the given id */
  expr::term_ref get_type(std::string id) const;

  /** Returns the a variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Get the string of a token begin parsed */
  std::string token_text(pANTLR3_COMMON_TOKEN token) const;
};

}
}
