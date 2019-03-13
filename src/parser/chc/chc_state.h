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
#include "chc_system.h"

#include "command/command.h"

#include <iosfwd>

#include <antlr3.h>

namespace sally {

namespace parser {

enum chc_object {
  CHC_VARIABLE,
  CHC_TYPE,
  CHC_PREDICATE,
  CHC_OBJECT_LAST
};

/** State attached to the parser */
class chc_state {

  /** The context */
  const system::context& d_context;

  /** The CHC system we're building */
  chc_system d_system;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref_strong> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref_strong> d_types;

  /** Symbol table for predicates */
  utils::symbol_table<expr::term_ref_strong> d_functions;

  /** MB: Not sure why I need this, but for now I do*/
  bool d_finalized;

public:

  /** Construct the parser state */
  chc_state(const system::context& context);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Returns the context for the parser */
  const system::context& ctx() const { return d_context; }

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

  /** Returns the function with the given id */
  expr::term_ref get_function(std::string id) const;

  /** New variable */
  void declare_variable(std::string id, expr::term_ref type);

  /** New function (return type is the last argument type) */
  void declare_function(std::string id, const std::vector<expr::term_ref>& signature);

  /** Get the string of a token begin parsed */
  static
  std::string token_text(pANTLR3_COMMON_TOKEN token);

  /** Ensure that the object is declared = true/false locally, throw exception otherwise */
  void ensure_declared(std::string id, chc_object type, bool declared) const;

  /** Check if declared */
  bool is_declared(std::string id, chc_object type) const;

  /** Assert a CHC rule */
  void assert_chc(expr::term_ref head, expr::term_ref tail);

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Returns the final command (or throws execption if translatio not possible) */
  cmd::command* finalize();

};

}
}
