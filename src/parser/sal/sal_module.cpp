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
#include "parser/parser.h"

#include "utils/trace.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace parser {
namespace sal {

module::module(expr::term_manager& tm)
: d_variables("variables")
, d_tm(tm)
{
}

module::~module()
{}

void module::add_parameter(std::string id, expr::term_ref var) {
  if (d_variables.has_entry(id)) {
    throw parser_exception(id + " already declared");
  }
  d_variables.add_entry(id, var);
  d_parameters.push_back(var);
  d_vars_parameter.insert(var);
}

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
  case SAL_VARIABLE_GLOBAL:
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

bool module::has_variable(std::string id, variable_class sal_var_class) const {
  if (!d_variables.has_entry(id)) return false;
  expr::term_ref var = d_variables.get_entry(id);
  variable_class_map::const_iterator find = d_variable_class.find(var);
  assert(find != d_variable_class.end());
  return find->second == sal_var_class;
}

void module::change_variable_class(std::string id, variable_class sal_var_class) {
  assert(has_variable(id, sal_var_class));
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
  case SAL_VARIABLE_GLOBAL:
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

void module::load_variables_into(symbol_table& table) const {
  table.load_from(d_variables);
}

#define insert_from_module(S, m) S.insert(m.S.begin(), m.S.end())

void module::load(const module& m) {

  // Copy over the symbol table
  m.load_variables_into(d_variables);

  // Parameters
  d_parameters.insert(d_parameters.end(), m.d_parameters.begin(), m.d_parameters.end());
  insert_from_module(d_vars_parameter, m);

  // Variables sets
  insert_from_module(d_vars_input, m);
  insert_from_module(d_vars_output, m);
  insert_from_module(d_vars_local, m);
  insert_from_module(d_vars_global, m);

  // Variables classes
  insert_from_module(d_variable_class, m);

  // Semantics
  insert_from_module(d_definitions, m);
  insert_from_module(d_initializations, m);
  insert_from_module(d_transitions, m);
}

module::ref module::instantiate(const std::vector<expr::term_ref>& actuals) const {
  assert(actuals.size() > 0);
  if (d_parameters.size() != actuals.size()) {
    throw parser_exception("actuals don't match the module parameters");
  }
  for (size_t i = 0; i < d_parameters.size(); ++ i) {
    if (!d_tm.compatible(d_parameters[i], actuals[i])) {
      std::stringstream ss;
      ss << "argument " << i + 1 << " doesn't match the module parameter type";
      throw parser_exception(ss.str());
    }
  }
  assert(false);
  return module::ref();
}

std::ostream& operator << (std::ostream& out, variable_class var_class) {
  switch (var_class) {
  case SAL_VARIABLE_INPUT:
    out << "INPUT";
    break;
  case SAL_VARIABLE_OUTPUT:
    out << "OUTPUT";
    break;
  case SAL_VARIABLE_LOCAL:
    out << "LOCAL";
    break;
  case SAL_VARIABLE_GLOBAL:
    out << "GLOBAL";
    break;
  default:
    assert(false);
  }

  return out;
}

void term_set_to_stream(std::ostream& out, const module::term_set& s) {
  module::term_set::const_iterator it = s.begin(), end = s.end();
  for (; it != end; ++ it) {
    out << " " << *it;
  }
}

void module::to_stream(std::ostream& out) const {
  out << "MODULE " << d_name << std::endl;

  if (d_parameters.size() > 0) {
    out << "parameters";
    for (size_t i = 0; i < d_parameters.size(); ++ i) {
      out << " " << d_parameters[i];
    }
    out << std::endl;
  }

  if (d_variables.size() > 0) {
    out << "variables";
    symbol_table::const_iterator it = d_variables.begin(), end = d_variables.end();
    for (; it != end; ++ it) {
      expr::term_ref var = it->second.back();
      out << " " << var;
      variable_class_map::const_iterator find = d_variable_class.find(var);
      if (find != d_variable_class.end()) {
        out << " " << find->second;
      }
    }
    out << std::endl;
  }

  if (d_definitions.size() > 0) {
    out << "definitions";
    term_set_to_stream(out, d_definitions);
    out << std::endl;
  }

  if (d_transitions.size() > 0) {
    out << "transitions";
    term_set_to_stream(out, d_transitions);
    out << std::endl;
  }

  if (d_initializations.size() > 0) {
    out << "initializations";
    term_set_to_stream(out, d_initializations);
    out << std::endl;
  }
}

std::ostream& operator << (std::ostream& out, const module& m) {
  m.to_stream(out);
  return out;
}

void module::add_definition(expr::term_ref definition) {
  const expr::term& t = d_tm.term_of(definition);
  if (t.op() == expr::TERM_AND) {
    for (size_t i = 0; i < t.size(); ++ i) {
      add_definition(t[i]);
    }
  } else {
    TRACE("parser::sal") << "module::add_definition: " << definition << std::endl;
    d_transitions.insert(definition);
  }
}

void module::add_initialization(expr::term_ref initialization) {
  const expr::term& t = d_tm.term_of(initialization);
  if (t.op() == expr::TERM_AND) {
    for (size_t i = 0; i < t.size(); ++ i) {
      add_initialization(t[i]);
    }
  } else {
    TRACE("parser::sal") << "module::add_initialization: " << initialization << std::endl;
    d_initializations.insert(initialization);
  }
}

void module::add_transition(expr::term_ref transition) {
  const expr::term& t = d_tm.term_of(transition);
  if (t.op() == expr::TERM_AND) {
    for (size_t i = 0; i < t.size(); ++ i) {
      add_transition(t[i]);
    }
  } else {
    TRACE("parser::sal") << "module::add_transition: " << transition << std::endl;
    d_transitions.insert(transition);
  }
}

void module::compose(const module& m_from, composition_type type, const std::vector<expr::term_ref>& index_vars) {
  load(m_from);
  std::cerr << "TODO: composition" << std::endl;
}

module::ref module::compose(const module& other, composition_type type) {

  TRACE("sal::module") << "compose: M1, M2" << std::endl;
  TRACE("sal::module") << "[M1 = " << *this << std::endl << "]" << std::endl;
  TRACE("sal::module") << "[M2 = " << other << std::endl << "]" << std::endl;

  module::ref result = new module(d_tm);
  result->load(*this);
  result->load(other);
  std::cerr << "TODO: composition" << std::endl;
  return result;
}

const module::symbol_table& module::get_symbol_table() const {
  return d_variables;
}

}
}
}


