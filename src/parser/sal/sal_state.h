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
#include "parser/command.h"
#include "parser/sal/sal_module.h"

#include <iosfwd>

#include <antlr3.h>

namespace sally {

namespace parser {

/** Types of model-checking obligations */
enum sal_assertion_form {
  SAL_OBLIGATION,
  SAL_CLAIM,
  SAL_LEMMA,
  SAL_THEOREM
};

/** Types of SAL objects that we keep in the symbol tables */
enum sal_object {
  SAL_VARIABLE,
  SAL_TYPE,
  SAL_MODULE,
  SAL_OBJECT_LAST
};

/** State attached to the parser */
class sal_state {

  /** The context */
  const system::context& d_context;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref_strong> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

  /** Symbol table for modules */
  utils::symbol_table<sal::module::ref> d_modules;

public:

  /** Construct the parser state */
  sal_state(const system::context& context);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Returns the context for the parser */
  const system::context& ctx() const { return d_context; }

  /** Create a new state type. */
  system::state_type* mk_state_type(std::string id,
      const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
      const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types) const;

  /** Create a new state formula */
  system::state_formula* mk_state_formula(std::string id, std::string type_id, expr::term_ref sf) const;

  /** Create a new transition formula */
  system::transition_formula* mk_transition_formula(std::string id, std::string type_id, expr::term_ref tf) const;

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
  void ensure_declared(std::string id, sal_object type, bool declared);

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Finalize parsing and return a command representing all the queries */
  command* finalize();

  /** Make a rational from the token */
  expr::term_ref token_to_rational(pANTLR3_COMMON_TOKEN token);
};

}
}
