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

#include "sal_module.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace parser {
namespace sal {

module::module(expr::term_manager& tm, std::string name)
: d_name(name)
, d_variables(name)
, d_tm(tm)
{
}

module::~module()
{}


void module::add_variable(std::string id, expr::term_ref var, variable_class sal_var_class) {

  typedef std::pair<term_set::iterator, bool> insert_return;

  insert_return r;

  // Add to the right symbol table
  switch (sal_var_class) {
  case SAL_VARIABLE_INPUT:
    r = d_vars_input.insert(var);
    assert(d_vars_output.find(var) == d_vars_output.end());
    assert(d_vars_local.find(var) == d_vars_local.end());
    assert(d_vars_global.find(var) == d_vars_global.end());
    break;
  case SAL_VARIABLE_OUTPUT:
    r = d_vars_output.insert(var);
    assert(d_vars_input.find(var) == d_vars_input.end());
    assert(d_vars_local.find(var) == d_vars_local.end());
    assert(d_vars_global.find(var) == d_vars_global.end());
    break;
  case SAL_VARIABLE_LOCAL:
    r = d_vars_local.insert(var);
    assert(d_vars_input.find(var) == d_vars_input.end());
    assert(d_vars_output.find(var) == d_vars_output.end());
    assert(d_vars_global.find(var) == d_vars_global.end());
    break;
  case SAL_VARIBALE_GLOBAL:
    r = d_vars_global.insert(var);
    assert(d_vars_input.find(var) == d_vars_input.end());
    assert(d_vars_output.find(var) == d_vars_output.end());
    assert(d_vars_local.find(var) == d_vars_local.end());
    break;
  }

  // Shouldn't have been there
  assert(r.second);

  // Add to symbol table
  d_variables.add_entry(id, var);

  // Mark the variable's class
  d_variable_class[var] = sal_var_class;
}

expr::term_ref module::get_variable(std::string id) const {
  assert(d_variables.has_entry(id));
  return d_variables.get_entry(id);
}

const module::term_set& module::get_variables(variable_class sal_var_class) const {
  switch (sal_var_class) {
  case SAL_VARIABLE_INPUT:
    return d_vars_input;
  case SAL_VARIABLE_OUTPUT:
    return d_vars_output;
  case SAL_VARIABLE_LOCAL:
    return d_vars_local;
  case SAL_VARIBALE_GLOBAL:
    return d_vars_global;
  default:
    assert(false);
    return d_vars_global;
  }
}

variable_class module::get_variable_class(expr::term_ref var) const {
  variable_class_map::const_iterator find = d_variable_class.find(var);
  assert(find != d_variable_class.end());
  return find->second;
}

}
}
}


