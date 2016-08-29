/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"
#include "system/context.h"
#include "utils/symbol_table.h"


#include <iosfwd>
#include <stack>

#include <antlr3.h>

namespace sally {

namespace parser {

enum mcmt_object {
  MCMT_VARIABLE,
  MCMT_TYPE,
  MCMT_STATE_TYPE,
  MCMT_STATE_FORMULA,
  MCMT_TRANSITION_FORMULA,
  MCMT_TRANSITION_SYSTEM,
  MCMT_PROCESS_TYPE,
  MCMT_OBJECT_LAST
};

/** State attached to the parser */
class mcmt_state {

  /** The context */
  const system::context& d_context;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref_strong> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

  typedef std::list<std::pair<std::string, expr::term_ref> >  lambda_variables_list;

  lambda_variables_list lambda_variables;

public:

  /** Construct the parser state */
  mcmt_state(const system::context& context);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Returns the context for the parser */
  const system::context& ctx() const { return d_context; }

  /** Create a new state type. */
  system::state_type* mk_state_type(std::string id,
      const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
      const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types) const;

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

  /**
   * Use the state type, both current, next, and the transitions.
   */
  void use_state_type_and_transitions(const system::state_type* state_type);

  /** Push a new scope for local declarations */
  void push_scope();

  /** Pop the locate declarations */
  void pop_scope();

  /** Returns the type with the given id */
  expr::term_ref get_type(std::string id) const;

  /** Returns the bit-vector type of the given size */
  expr::term_ref get_bitvector_type(size_t size) const;

  /** Returns the a variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Sets the variable to a given term */
  void set_variable(std::string id, expr::term_ref t);

  /**
   * Make a condition term:
   * if c[0] then c[1]
   * if c[2] then c[3]
   * ...
   * else c[2n]
   */
  expr::term_ref mk_cond(const std::vector<expr::term_ref>& children);

  /** Get the string of a token begin parsed */
  static
  std::string token_text(pANTLR3_COMMON_TOKEN token);

  /** Ensure that the object is declared = true/false locally, throw exception otherwise */
  void ensure_declared(std::string id, mcmt_object type, bool declared) const;

  /** Check if declared */
  bool is_declared(std::string id, mcmt_object type) const;

  /** Are we using lsal extensions (a' for next.a, a for state.a, cond operator) */
  bool lsal_extensions() const;

  /** Are we not namespacing the input variables (x instead of input.x) */
  bool no_input_namespace() const;

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  void mk_process_type(std::string id);

  expr::term_ref mk_array_type(expr::term_ref from, expr::term_ref to);

  void push_lambda(std::string, expr::term_ref);
  void pop_lambda();

};

}
}
