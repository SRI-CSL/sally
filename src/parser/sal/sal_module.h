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

#include <iosfwd>
#include <string>
#include <set>
#include <vector>

#include "expr/term.h"
#include "expr/term_map.h"
#include "expr/term_manager.h"
#include "utils/smart_ptr.h"
#include "utils/symbol_table.h"
#include "system/transition_system.h"

namespace sally {
namespace parser {
namespace sal {

/** Types of variables */
enum variable_class {
  SAL_VARIABLE_INPUT,
  SAL_VARIABLE_OUTPUT,
  SAL_VARIABLE_LOCAL,
  SAL_VARIABLE_GLOBAL
};

/** Types of composition */
enum composition_type {
  SAL_COMPOSE_SYNCHRONOUS,
  SAL_COMPOSE_ASYNCHRONOUS
};

std::ostream& operator << (std::ostream& out, variable_class var_class);

std::ostream& operator << (std::ostream& out, composition_type comp_type);

/**
 * Base module functionality so that we can pass around different kinds of
 * modules.
 */
class module {

public:

  typedef std::set<expr::term_ref> term_set;
  typedef expr::term_ref_hash_map<variable_class> variable_class_map;
  typedef expr::term_ref_hash_map<expr::term_ref> term_to_term_map;
  typedef utils::symbol_table<expr::term_ref> symbol_table;

  enum symbol_override {
    /** Symbol overrride is not allowed (throws) */
    SYMBOL_OVERRIDE_NO,
    /** Symbol overrride is allowed unless they are equal in type and class */
    SYMBOL_OVERRIDE_YES_EQ,
    /** Symbol override is allowed */
    SYMBOL_OVERRIDE_YES
  };

  /** Structure to carry term, with its next version */
  struct lvalue_info {
    expr::term_ref x, x_next;
    variable_class var_class;
    lvalue_info(): var_class(SAL_VARIABLE_LOCAL) {}
    lvalue_info(expr::term_ref x, expr::term_ref x_next, variable_class var_class)
    : x(x), x_next(x_next), var_class(var_class) {}
  };

  typedef std::map<std::string, lvalue_info> id_to_lvalue;

private:

  /** Name of the module */
  std::string d_name;

  /** Symbol table */
  symbol_table d_variables;

  /** List of parameters, in order they were added */
  std::vector<expr::term_ref> d_parameters;

  /** List of parameter variables */
  term_set d_vars_parameter;

  /** List of input variables */
  term_set d_vars_input;

  /** List of output variables */
  term_set d_vars_output;

  /** List of local variables */
  term_set d_vars_local;

  /** List of global variables */
  term_set d_vars_global;

  /** Map from variables to the class they belong to */
  variable_class_map d_variable_class;

  /** Map from variables to their next version (if any) */
  term_to_term_map d_variable_next;

  /** Term manager we're using */
  expr::term_manager& d_tm;

  term_set d_definitions;
  term_set d_initializations;
  term_set d_transitions;

  /** Insert to set with substitution */
  void insert_with_substitution(term_set& to, const term_set& from, const expr::term_manager::substitution_map& subst);

  /** Insert to map with substitution */
  void insert_with_substitution(term_to_term_map& to, const term_to_term_map& from, const expr::term_manager::substitution_map& subst);

  /** Insert to map with substitution */
  void insert_with_substitution(variable_class_map& to, const variable_class_map& from, const expr::term_manager::substitution_map& subst);

  /** Insert to vector with substitution */
  void insert_with_substitution(std::vector<expr::term_ref>& to, const std::vector<expr::term_ref>& from, const expr::term_manager::substitution_map& subst);

  /** Insert to symbol table with substitution. Also, skip given symbols. */
  void insert_with_substitution(module& to, const module& from, const std::set<std::string>& to_skip, const expr::term_manager::substitution_map& subst, symbol_override allow_override);

  /** Finish composition after loading all the ingredients */
  void finish_symbol_composition(composition_type type, expr::term_manager::substitution_map& subst);

  /** Load the symbols from another module, skip given */
  void load_symbols(const module& m, const std::set<std::string>& to_skip, const expr::term_manager::substitution_map& subst_map, symbol_override allow_override);

  /** Load the semantics from another module */
  void load_semantics(const module& m, const expr::term_manager::substitution_map& subst_map);

  /** Load disjunctive semantics from another module */
  void load_semantics(const module& m1, const module& m2, const expr::term_manager::substitution_map& subst_map);

  /** Returns the idle transition (x' = x) of the module */
  expr::term_ref get_idle() const;

  /**
   * Removes the variable from internal structures (not from symbol table).
   * Returns true if variable had a next.
   */
  void remove_variable(expr::term_ref var, variable_class sal_var_class);

public:

  module(expr::term_manager& tm);
  ~module();

  /** Set the name of the module */
  void set_name(std::string name) { d_name = name; }

  /** Get the name of the module */
  std::string get_name() const { return d_name; }

  /** Smart references to modules */
  typedef utils::smart_ptr<module> ref;

  /** Add a parameter to the module */
  void add_parameter(std::string id, expr::term_ref var);

  /** Returns true if the term is a module parameter */
  bool is_parameter(expr::term_ref var) const;

  /** Add a variable to the module */
  void add_variable(std::string id, expr::term_ref var, variable_class sal_var_class, expr::term_ref var_next);

  /** Is there a variable with the given id */
  bool has_variable(std::string id) const;

  /** Check if module has a variable named id and it is of the given class */
  bool has_variable(std::string id, variable_class sal_var_class) const;

  /** Change a class of a variable */
  void change_variable_class(std::string id, variable_class sal_var_class);

  /** Get the variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Check if a variable is from this module */
  bool has_variable(expr::term_ref var) const;

  /** Get next variable if there is one (throws if not) */
  bool has_next_variable(expr::term_ref var) const;

  /** Get next variable if there is one (throws if not) */
  expr::term_ref get_next_variable(expr::term_ref var) const;

  /** Get the class of a variable (throws if not a state variable) */
  variable_class get_variable_class(expr::term_ref var) const;

  /**
   * Check if the term is an lvalue in this module. A term is an lvalue
   * if it's a variable in the module, or a read from an lvalue.
   */
  bool is_lvalue(expr::term_ref lvalue) const;

  /** Get the class of an lvalue (throws if not a state lvalue) */
  variable_class get_lvalue_class(expr::term_ref lvalue) const;

  /** Get all variables of a class */
  const term_set& get_variables(variable_class sal_var_class) const;

  /** Get all variables of a class */
  template <typename collection>
  void get_variables(variable_class sal_var_class, collection& out) const;

  /** Get the symbol table */
  const symbol_table& get_symbol_table() const;

  /** Flatten the module into a flat module */
  module::ref flatten();

  /** Get the term manager of the module */
  expr::term_manager& tm() const { return d_tm; }

  /** Load the current module variables into the symbol table */
  void load_variables_into(symbol_table& table) const;

  /**
   * Load another module into this module (i.e. add all tables, initialization,
   * ...). If allow_override is true, adding duplicate variables (of conflicting
   * type is allowed.
   */
  void load(const module& m, symbol_override allow_override);

  /**
   * Load another module into this module (i.e. add all tables, initialization,
   * ...). If allow_override is true, adding duplicate variables (of conflicting
   * type is allowed.
   */
  void load(const module& m, const id_to_lvalue& subst, symbol_override allow_override);

  /** Instantiate the module with the given parameters */
  module::ref instantiate(const std::vector<expr::term_ref>& actuals) const;

  /** Output the module information to the stream */
  void to_stream(std::ostream& out) const;

  /** Add a definition */
  void add_definition(expr::term_ref definition);

  /** Returns all definitions */
  const term_set& get_definitions() { return d_definitions; }

  /** Add an initialization */
  void add_initialization(expr::term_ref initialization);

  /** Returns all initializations */
  const term_set& get_initializations() { return d_initializations; }

  /** Add a transition */
  void add_transition(expr::term_ref transition);

  /** Return all transitions */
  const term_set& get_transitions() { return d_transitions; }

  /** Perform composition over given index variables */
  void compose(const module& m_from, composition_type type, const std::vector<expr::term_ref>& index_vars);

  /** Return a module that is a composition of this module and another module */
  module::ref compose(const module& other, composition_type type);

  /** Check module invariants (debugging) */
  void check_invariants() const;
};

std::ostream& operator << (std::ostream& out, const module& m);

template <typename collection>
void module::get_variables(variable_class sal_var_class, collection& out) const {
  const term_set& vars = get_variables(sal_var_class);
  std::copy(vars.begin(), vars.end(), std::insert_iterator<collection>(out, out.end()));
}

}
}
}
