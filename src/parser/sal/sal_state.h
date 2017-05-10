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
#include "parser/sal/sal_context.h"
#include "parser/sal/sal_module.h"

#include <iosfwd>

#include <antlr3.h>

namespace sally {
namespace parser {

/** Helper for variable declaration lists */
struct var_declarations_ctx {

  std::vector<std::string> var_names;
  std::vector<expr::term_ref> var_types;

  size_t size() const { return var_names.size(); }

  void add(std::string name, expr::term_ref type);
  void add(std::string name);
  void add(expr::term_ref type);
};

/** Types of SAL objects that we keep in the symbol tables */
enum sal_object {
  SAL_VARIABLE,
  SAL_TYPE,
  SAL_MODULE,
  SAL_OBJECT_LAST
};

enum scope_type {
  SCOPE_MODULE,
  SCOPE_MODULE_DECLARATION,
  SCOPE_PREDICATE_SUBTYPE,
  SCOPE_QUANTIFIER,
  SCOPE_INDEXED_COMPOSITION,
  SCOPE_INDEXED_ARRAY,
  SCOPE_LAMBDA,
  SCOPE_SET_ABSTRACTION,
  SCOPE_ASSERTION,
  SCOPE_LET
};

/** State attached to the parser */
class sal_state {

  /** The context */
  const system::context& d_context;

  /** SAL context */
  sal::context* d_sal_context;

  /** Symbol table for variables */
  utils::symbol_table<expr::term_ref> d_variables;

  /** Symbol table for types */
  utils::symbol_table<expr::term_ref> d_types;

  /** Symbol table for modules */
  utils::symbol_table<sal::module::ref> d_modules;

  /** Current module stack */
  std::vector<sal::module::ref> d_current_module;

  expr::term_ref d_boolean_type;
  expr::term_ref d_integer_type;
  expr::term_ref d_natural_type;
  expr::term_ref d_nznat_type;
  expr::term_ref d_real_type;

  /** Variable for subrange types */
  expr::term_ref d_x;

  typedef expr::term_ref_hash_map<expr::term_ref> term_to_term_map;

  /** Map from functions to their definitions */
  term_to_term_map d_fun_to_definition_map;

  /** Map from variable to their next version */
  term_to_term_map d_var_to_next_map;

  /** Map from next variable to their next version */
  term_to_term_map d_next_to_var_map;

  /** Create a new variable and it's next version */
  expr::term_ref new_variable(std::string name, expr::term_ref type, bool has_next);

  /** Tracking of lvalues for command blocks */
  std::set<expr::term_ref> d_lvalues;
  
  /** Are lvalues passed in as next variables? */
  bool d_in_transition;

  /** Tracking guards, so that we can make an ELSE case */
  std::set<expr::term_ref> d_guards;

  /** Scopes we work on */
  std::vector<scope_type> d_scope;

  /** Depth of multi-command */
  size_t d_multi_commands;

  /** Guard of the multi-command */
  expr::term_ref d_multi_guard;

public:

  /** Construct the parser state */
  sal_state(const system::context& context);

  /** Finalize parsing and return a command representing all the queries */
  cmd::command* finalize();

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Basic types */
  expr::term_ref boolean_type() { return d_boolean_type; }
  expr::term_ref integer_type() { return d_integer_type; }
  expr::term_ref natural_type() { return d_natural_type; }
  expr::term_ref nznat_type() { return d_nznat_type; }
  expr::term_ref real_type() { return d_real_type; }

  /** Returns the context for the parser */
  const system::context& ctx() const { return d_context; }

  /** Push a new scope in variable and type symbol tables */
  void push_scope(scope_type type);

  /** Pop a scope in variable and type symbol tables */
  void pop_scope(scope_type type);

  /** Get a type (throw exception if not found) */
  expr::term_ref get_type(std::string id) const;

  /** Get a variable (throw exception if not found) */
  expr::term_ref get_variable(std::string name, bool next) const;

  /** Ensure the term is a variable in the current module */
  void ensure_variable(expr::term_ref x, bool next) const;

  /** Get the next state version of the variable */
  expr::term_ref get_next_state_variable(expr::term_ref var) const;

  /** Get the state version from the next-state variable */
  expr::term_ref get_state_variable(expr::term_ref next_var) const;

  /** Get a module (throw exception if not found) */
  sal::module::ref get_module(std::string name, const std::vector<expr::term_ref>& actuals);

  /** Define a variable id -> term in the symbol table */
  void define_var_in_scope(std::string id, expr::term_ref type, expr::term_ref term);

  /** Define a type id -> type in the symbol table */
  void define_type_in_scope(std::string id, expr::term_ref type);

  /** Define a constant in the SAL context */
  void define_constant(std::string id, expr::term_ref type, expr::term_ref term);

  /** Declare a constant in the SAL context */
  void declare_constant(std::string id, expr::term_ref type);

  /** Define type in the SAL context */
  void define_type(std::string id, expr::term_ref type);

  /** Get the string of a token begin parsed */
  static
  std::string token_text(pANTLR3_COMMON_TOKEN token);

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Create a new context */
  void new_context(std::string name);

  /** Return the current context */
  sal::context* get_context() const;

  /** Return a new module and push scope */
  sal::module::ref start_module();

  /** Finalize module and pop scope */
  void finish_module(sal::module::ref m);

  /** Add parameters to SAL context */
  void add_context_parameters(const var_declarations_ctx& vars);

  /** Make an integer from the token */
  expr::rational mk_integer(pANTLR3_COMMON_TOKEN token);

  /** Make an integer from the token1 '.' token2 */
  expr::rational mk_rational(pANTLR3_COMMON_TOKEN token1, pANTLR3_COMMON_TOKEN token2);

  /** Make an rational constant */
  expr::term_ref mk_rational_constant(const expr::rational& rat);

  /** Make a Boolean constant */
  expr::term_ref mk_boolean_constant(bool value);

  /** Make a string constant */
  expr::term_ref mk_string(std::string s);

  /** Make a term given the children */
  expr::term_ref mk_term(expr::term_op, expr::term_ref child);

  /** Make a term given the children */
  expr::term_ref mk_term(expr::term_op, expr::term_ref child1, expr::term_ref child2);

  /** Make a tuple */
  expr::term_ref mk_tuple(const std::vector<expr::term_ref>& elements);

  /** Make a record */
  expr::term_ref mk_record(const expr::term_manager::id_to_term_map& content);

  /** Make an array read */
  expr::term_ref mk_array_read(expr::term_ref a, expr::term_ref i);

  /** Make a record read */
  expr::term_ref mk_record_read(expr::term_ref base, expr::term_ref id);

  /** Make an ITE from the vector of conditions/terms */
  expr::term_ref mk_ite(const std::vector<expr::term_ref>& ite_terms);

  /** Make a subrange type [b1, ..., b2]. If bi is null it is +-\infty */
  expr::term_ref mk_subrange_type(expr::term_ref b1, expr::term_ref b2);

  /** Make a single select */
  expr::term_ref mk_term_access(expr::term_ref base, expr::term_ref accessor);

  /** Make a sequence of selects */
  expr::term_ref mk_term_access(expr::term_ref base, const std::vector<expr::term_ref>& accessors);

  /** Make a single update */
  expr::term_ref mk_term_update(expr::term_ref base, expr::term_ref accessor, expr::term_ref value);

  /** Make a sequence of updates starting from i-th */
  expr::term_ref mk_term_update(expr::term_ref base, size_t i, const std::vector<expr::term_ref>& accessors, expr::term_ref value);

  /** Make a sequence of updates */
  expr::term_ref mk_term_update(expr::term_ref base, const std::vector<expr::term_ref>& accessors, expr::term_ref value);

  /** Make a function application */
  expr::term_ref mk_fun_app(expr::term_ref f, const std::vector<expr::term_ref>& args);

  /** Add an assertion to check */
  void add_assertion(std::string id, sal::assertion_form form, sal::module::ref m, expr::term_ref assertion);

  /** Make a predicate subtype using the state's abstractino helper */
  expr::term_ref mk_predicate_subtype(expr::term_ref body);

  /** Make an enumerated type */
  expr::term_ref mk_enum_type(const std::vector<std::string>& id_set);

  /** Register enumeration values as variables */
  void register_enumeration(expr::term_ref enum_type);

  /** Make an array type */
  expr::term_ref mk_array_type(expr::term_ref index_type, expr::term_ref element_type);

  /** Make a record type */
  expr::term_ref mk_record_type(const var_declarations_ctx& elements);

  /** Start a constant declaration */
  void start_constant_declaration(std::string id, const var_declarations_ctx& args, expr::term_ref type);

  /** Finish a constant declaration */
  void finish_constant_declaration(std::string id, const var_declarations_ctx& args, expr::term_ref type, expr::term_ref definition);

  /** Start a module declaration */
  void start_module_declaration(const var_declarations_ctx& args);

  /** Finish module declaration */
  void finish_module_declaration(sal::module::ref m, const var_declarations_ctx& args);

  /** Define a module */
  void define_module(std::string id, sal::module::ref m);

  /** Start a definitino of predicate subtype */
  void start_predicate_subtype(std::string id, expr::term_ref base_type);

  /** Finish a predicate subtype definitions */
  expr::term_ref finish_predicate_subtype(expr::term_ref predicate);

  /** Start construction of a quantifier */
  void start_quantifier(const var_declarations_ctx& bindings);

  /** Make a quantifier of a previously started quantifier (doesn't finish) */
  expr::term_ref mk_quantifier(expr::term_op op, expr::term_ref body);

  /** Finish construction of a previously started quantifier */
  expr::term_ref finish_quantifier(expr::term_op op, expr::term_ref body);

  /** Start construction of an indexed composition */
  void start_indexed_composition(const var_declarations_ctx& bindings);

  /** Finish construction of a previously started indexed composition */
  void finish_indexed_composition(sal::module::ref m_from, sal::module::ref m_into, sal::composition_type comp_type);

  /** Start construction of a lambda (adds to abstraction helper) */
  void start_lambda(const var_declarations_ctx& bindings);

  /** Finish construction of a previously started lambda */
  expr::term_ref finish_lambda(expr::term_ref body);

  /** Start set abstraction lhs = { id : type | ... } */
  void start_set_abstraction(expr::term_ref lhs, std::string id, expr::term_ref type);

  /** End set abstraction */
  void end_set_abstraction();

  /** Start an indexed array with the given declaration */
  void start_indexed_array(const var_declarations_ctx& bindings);

  /** Finish an indexed array */
  expr::term_ref finish_indexed_array(expr::term_ref body);

  /** Make a set enumeration t in { e1, ..., en} : t = e1 || t = e2 || ... || t = en*/
  expr::term_ref mk_set_enumeration(expr::term_ref t, const std::vector<expr::term_ref>& set_elements);

  /** Add to map and make sure check that the names are not clashing with each other */
  static
  void add_to_map(expr::term_manager::id_to_term_map& map, std::string id, expr::term_ref t);

  /** Create a module that is a composition of m1 and m2 */
  sal::module::ref composition(sal::module::ref m1, sal::module::ref m2, sal::composition_type);

  /** Declare variables in the scope */
  void declare_variables(const var_declarations_ctx& vars);

  /** Declare variables in the scope and in the module m */
  void declare_variables(sal::module::ref m, sal::variable_class var_class, const var_declarations_ctx& vars);

  /** Load the module variables into the state */
  void load_module_variables(sal::module::ref m);

  /**
   * Load the module m_from content to the module m_to. If allow_override is
   * true, duplicate variables are allowed.
   */
  void load_module_to_module(sal::module::ref m_from, sal::module::ref m_to, bool allow_override);

  /**
   * Load the module m_from content to the module m_to while applying the given
   * renaming. If allow_override is true, duplicate variables are allowed.
   */
  void load_module_to_module(sal::module::ref m_from, sal::module::ref m_to, const expr::term_manager::id_to_term_map& subst, bool allow_override);

  /** Change given module variables to the given class */
  void change_module_variables_to(sal::module::ref m, const var_declarations_ctx& vars, sal::variable_class var_class);

  /** Start an initialization block (to collect lvalues) */
  void start_initialization();

  /** Add a new initialization to m (uses and clears lvalues) */
  void add_initialization(sal::module::ref m, expr::term_ref initialization);
  
  /** End the initialization block */
  void end_initialization();

  /** Start a definition block */
  void start_definition();

  /** Add a new definition to m (lvalues are all lvalues in this definition) */
  void add_definition(sal::module::ref m, expr::term_ref definition);

  /** End a definition block */
  void end_definition();

  /** Start a transition block */
  void start_transition();

  /** Add a new transition to m (lvalues are all lvalues in this definition) */
  void add_transition(sal::module::ref m, expr::term_ref transition);

  /** End a transition block */
  void end_transition();

  /** Make a term from a list of commands (guarder and multi) */
  expr::term_ref mk_term_from_commands(const std::vector<expr::term_ref>& cmds, bool has_else);

  /**
   * Make a term from a guarded command (single guard, vector of assignments).
   * Guard can be null to cover the else case.
   */
  expr::term_ref mk_term_from_guarded(expr::term_ref guard, const std::vector<expr::term_ref>& assignments);

  /** Make an assignment. If an assignmnet of a read term, convert to update term. */
  expr::term_ref mk_assignment(expr::term_ref lvalue, expr::term_ref rhs);

  /** Check that the term is OK */
  void check_term(expr::term_ref t) const;

  /** Check that the index type is really an index type */
  void check_index_type(expr::term_ref t) const;

  /** Add an lvalue to the set of lvalues and do some checking */
  void lvalues_add(expr::term_ref t);

  /** Clear lvalues */
  void lvalues_clear();

  /** Add a guard to the set of guards and do some checking */
  void guards_add(expr::term_ref t);

  /** Clear guards */
  void guards_clear();

  /** Start a multicommand (count quantifiers so that we can extract the quantified guard) */
  void start_multi_command();

  /** End a multicommand */
  void end_multi_command();

};

}
}
