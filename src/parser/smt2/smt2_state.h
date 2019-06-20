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
#include "command/command.h"


#include <iosfwd>

#include <antlr3.h>

namespace sally {

namespace parser {

enum smt2_object {
  SMT2_VARIABLE,
  SMT2_TYPE,
  SMT2_OBJECT_LAST
};

/** State attached to the parser */
class smt2_state {

  /** The context */
  const system::context& d_context;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref> d_types;

  /** List of globally declared variables */
  std::vector<std::string> d_variable_ids;
  std::vector<expr::term_ref> d_variable_terms;
  std::vector<expr::term_ref> d_variable_types;

  /** All assertions */
  std::vector<expr::term_ref> d_assertions;

public:

  /** Construct the parser state */
  smt2_state(const system::context& context);

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

  expr::term_ref mk_rational_constant(std::string number);

  /** Ensure that the object is declared = true/false locally, throw exception otherwise */
  void ensure_declared(std::string id, smt2_object type, bool declared) const;

  /** Check if declared */
  bool is_declared(std::string id, smt2_object type) const;

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Make the system */
  cmd::command* mk_smt2_system();

  void assert_command(expr::term_ref f);
  void declare_variable(std::string id, expr::term_ref type);
  void set_variable(std::string id, expr::term_ref t);

};

}
}
