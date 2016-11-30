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
  SAL_VARIBALE_GLOBAL
};

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

public:

  module(expr::term_manager& tm, std::string name);
  ~module();

  /** Smart references to modules */
  typedef utils::smart_ptr<module> ref;

  /** Add a variable to the module */
  void add_variable(std::string id, expr::term_ref var, variable_class sal_var_class);

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

};


}
}
}
