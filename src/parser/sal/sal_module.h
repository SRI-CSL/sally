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

/**
 * Base module functionality so that we can pass around different kinds of
 * modules.
 */
class module {

public:

  typedef std::set<expr::term_ref> term_set;
  typedef expr::term_ref_hash_map<variable_class> variable_class_map;
  typedef utils::symbol_table<expr::term_ref> symbol_table;

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

  /** Term manager we're using */
  expr::term_manager& d_tm;

  term_set d_definitions;
  term_set d_initializations;
  term_set d_transitions;

public:

  module(expr::term_manager& tm);
  ~module();

  /** Set the name of the module */
  void set_name(std::string name) { d_name = name; }

  /** Smart references to modules */
  typedef utils::smart_ptr<module> ref;

  /** Add a parameter to the module */
  void add_parameter(std::string id, expr::term_ref var);

  /** Add a variable to the module */
  void add_variable(std::string id, expr::term_ref var, variable_class sal_var_class);

  /** Check if module has a variable named id and it is of the given class */
  bool has_variable(std::string id, variable_class sal_var_class) const;

  /** Change a class of a variable */
  void change_variable_class(std::string id, variable_class sal_var_class);

  /** Get the variable with the given id */
  expr::term_ref get_variable(std::string id) const;

  /** Get the class of a variable */
  variable_class get_variable_class(expr::term_ref var) const;

  /** Get all variables of a class */
  const term_set& get_variables(variable_class sal_var_class) const;

  /** Get the symbol table */
  const symbol_table& get_symbol_table() const;

  /** Flatten the module into a flat module */
  module::ref flatten();

  /** Get the term manager of the module */
  expr::term_manager& tm() const { return d_tm; }

  /** Load the current module variables into the symbol table */
  void load_variables_into(symbol_table& table) const;

  /** Load another module into this module (i.e. add all tables, initialization, ...) */
  void load(const module& m);

  /** Instantiate the module with the given parameters */
  module::ref instantiate(const std::vector<expr::term_ref>& actuals) const;

  /** Output the module information to the stream */
  void to_stream(std::ostream& out) const;

  /** Add a definition */
  void add_definition(expr::term_ref definition);

  /** Add an initialization */
  void add_initialization(expr::term_ref initialization);

  /** Add a transition */
  void add_transition(expr::term_ref transition);

  /** Perform composition over given index variables */
  void compose(const module& m_from, composition_type type, const std::vector<expr::term_ref>& index_vars);

  /** Return a module that is a composition of this module and another module */
  module::ref compose(const module& other, composition_type type);

};

std::ostream& operator << (std::ostream& out, const module& m);

}
}
}
