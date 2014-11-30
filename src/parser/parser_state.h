/*
 * parser_state.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"
#include "system/context.h"
#include "utils/symbol_table.h"

#include <iosfwd>

#include <antlr3.h>

namespace sal2 {

namespace parser {

enum parser_object {
  PARSER_VARIABLE,
  PARSER_TYPE,
  PARSER_STATE_TYPE,
  PARSER_STATE_FORMULA,
  PARSER_TRANSITION_FORMULA,
  PARSER_TRANSITION_SYSTEM,
  PARSER_OBJECT_LAST
};

/** State attached to the parser */
class parser_state {

  /** The context */
  system::context& d_context;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

public:

  /** Construct the parser state */
  parser_state(system::context& context);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Returns the context for the parser */
  system::context& ctx() const { return d_context; }

  /** Report an error */
  void report_error(std::string msg) const;

  /** Create a new state type. */
  system::state_type* mk_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types) const;

  /** Create a new state formula */
  system::state_formula* mk_state_formula(std::string id, std::string type_id, expr::term_ref sf) const;

  /** Create a new transition formula */
  system::transition_formula* mk_transition_formula(std::string id, std::string type_id, expr::term_ref tf) const;

  /** Create a new transition system */
  system::transition_system* mk_transition_system(std::string id, std::string type_id, std::string init_id, const std::vector<std::string>& transition_ids);

  /**
   * Use the state type, i.e. declare the variables var_class.x, var_class.y, ...
   * If use_namespace is true, then "var_class." is not used in the name.
   */
  void use_state_type(std::string id, system::state_type::var_class var_class, bool use_namespace);

  /**
   * Use the state type, i.e. declare the variables var_class.x, var_class.y, ...
   * If use_namespace is true, then "var_class." is not used in the name.
   */
  void use_state_type(const system::state_type* state_type, system::state_type::var_class var_class, bool use_namespace);

  /** Push a new scope for local declarations */
  void push_scope();

  /** Pop the locate declarations */
  void pop_scope();

  /** Returns the type with the given id */
  expr::term_ref get_type(std::string id) const;

  /** Returns the a variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Get the string of a token begin parsed */
  static
  std::string token_text(pANTLR3_COMMON_TOKEN token);

  /** Ensure that the object is declared = true/false locally, throw exception otherwise */
  void ensure_declared(std::string id, parser_object type, bool declared);
};

}
}
