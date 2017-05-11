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
: d_variables("variables", false)
, d_tm(tm)
{
}

module::~module()
{}

void module::check_invariants() const {

  // 1. Only LOCAL variables can appear twice in the symbol table
  symbol_table::const_iterator it = d_variables.begin();
  for (; it != d_variables.end(); ++ it) {
    const symbol_table::T_list& entries = it->second;
    if (entries.size() > 1) {
      std::string var_id = it->first;
      symbol_table::T_list::const_iterator e_it = entries.begin();
      for (; e_it != entries.end(); ++ e_it) {
        expr::term_ref var = *e_it;
        if (get_variable_class(var) != SAL_VARIABLE_LOCAL) {
          throw parser_exception("multiple non-local " + var_id + " variables");
        }
      }
    }
  }

}



void module::add_parameter(std::string id, expr::term_ref var) {
  if (d_variables.has_entry(id)) {
    throw parser_exception(id + " already declared");
  }
  d_variables.add_entry(id, var);
  d_parameters.push_back(var);
  d_vars_parameter.insert(var);
}

bool module::is_parameter(expr::term_ref var) const {
  term_set::const_iterator find = d_vars_parameter.find(var);
  return find != d_vars_parameter.end();
}

void module::change_variable_class(expr::term_ref var, variable_class to_class) {
  variable_class from_class = get_variable_class(var);

  // Output and global variables can be made local by the LOCAL construct.
  if ((from_class == SAL_VARIABLE_OUTPUT || from_class == SAL_VARIABLE_GLOBAL) && to_class != SAL_VARIABLE_LOCAL) {
    throw parser_exception("OUTPUT and GLOBAL variables can only be made LOCAL.");
  }
  // Global variables can be made output by the OUTPUT construct
  if (from_class == SAL_VARIABLE_GLOBAL && to_class != SAL_VARIABLE_OUTPUT) {
    throw parser_exception("GLOBAL variables can only be made OUTPUT.");
  }

  term_set* to_erase = 0;
  term_set* to_insert = 0;

  if (to_class == SAL_VARIABLE_LOCAL) {
    if (from_class != SAL_VARIABLE_OUTPUT && from_class != SAL_VARIABLE_GLOBAL) {
      throw parser_exception("Only OUTPUT and GLOBAL variables can be made LOCAL.");
    }
    if (from_class == SAL_VARIABLE_OUTPUT) { to_erase = &d_vars_output; }
    if (from_class == SAL_VARIABLE_GLOBAL) { to_erase = &d_vars_global; }
    to_insert = &d_vars_local;
  }
  if (to_class == SAL_VARIABLE_OUTPUT) {
    if (from_class != SAL_VARIABLE_GLOBAL) {
      throw parser_exception("Only GLOBAL variables can be made OUTPUT.");
    }
    to_insert = &d_vars_output;
    to_erase = &d_vars_global;
  }

  assert(to_insert && to_erase);

  size_t erased = to_erase->erase(var);
  std::pair<term_set::iterator, bool> inserted = to_insert->insert(var);
  (void)erased;
  (void)inserted;
  assert(erased == 1);
  assert(inserted.second);
}

void module::remove_variable(expr::term_ref var, variable_class sal_var_class) {
  switch (sal_var_class) {
  case SAL_VARIABLE_INPUT:
    assert(d_vars_input.count(var) > 0);
    d_vars_input.erase(var);
    break;
  case SAL_VARIABLE_OUTPUT:
    assert(d_vars_output.count(var) > 0);
    d_vars_output.erase(var);
    break;
  case SAL_VARIABLE_LOCAL:
    assert(d_vars_local.count(var) > 0);
    d_vars_local.erase(var);
    break;
  case SAL_VARIABLE_GLOBAL:
    assert(d_vars_global.count(var) > 0);
    d_vars_global.erase(var);
    break;
  }

  // Mark the variable's class
  assert(d_variable_class.count(var) > 0);
  d_variable_class.erase(var);

  // If there is a next variable, remember it
  term_to_term_map::const_iterator next_find = d_variable_next.find(var);
  if (next_find != d_variable_next.end()) {
    d_variable_next.erase(next_find);
  }
}

void module::add_variable(std::string id, expr::term_ref var, variable_class sal_var_class, expr::term_ref var_next) {

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

  // If there is a next variable, remember it
  if (!var_next.is_null()) {
    d_variable_next[var] = var_next;
  }
}

bool module::has_variable(expr::term_ref var) const {
  return d_variable_class.find(var) != d_variable_class.end();
}

bool module::has_next_variable(expr::term_ref var) const {
  term_to_term_map::const_iterator find = d_variable_next.find(var);
  return (find != d_variable_next.end());
}

expr::term_ref module::get_next_variable(expr::term_ref var) const {
  term_to_term_map::const_iterator find = d_variable_next.find(var);
  if (find == d_variable_next.end()) {
    throw parser_exception(d_tm) << "Variable " << var << " doesn't have a next!";
  }
  return find->second;
}

expr::term_ref module::get_idle() const {
  term_set idle;
  term_to_term_map::const_iterator it = d_variable_next.begin();
  for (; it != d_variable_next.end(); ++ it) {
    expr::term_ref x = it->first;
    expr::term_ref x_next = it->second;
    expr::term_ref eq = d_tm.mk_term(expr::TERM_EQ, x, x_next);
    idle.insert(eq);
  }
  return d_tm.mk_and(idle);
}

bool module::has_variable(std::string id) const {
  return d_variables.has_entry(id);
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
  // Go throgh the variables and change the class
  const symbol_table::T_list& vars = d_variables.get_entries(id);
  symbol_table::T_list::const_iterator it = vars.begin();
  for (; it != vars.end(); ++ it) {
    expr::term_ref var = *it;
    change_variable_class(var, sal_var_class);
  }
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
  if (find == d_variable_class.end()) {
    throw parser_exception(d_tm) << "Expecting state variable, got " << var;
  }
  return find->second;
}

bool module::is_lvalue(expr::term_ref lvalue) const {
  const expr::term_op op = d_tm.op_of(lvalue);
  // Variable
  switch (op) {
  case expr::TERM_ARRAY_READ:
  case expr::TERM_RECORD_READ:
    return is_lvalue(d_tm.term_of(lvalue)[0]);
    break;
  case expr::VARIABLE:
    return has_variable(lvalue);
    break;
  default:
    throw parser_exception("not an lvalue");
  }
}

variable_class module::get_lvalue_class(expr::term_ref lvalue) const {
  const expr::term_op op = d_tm.op_of(lvalue);
  // Variable
  switch (op) {
  case expr::TERM_ARRAY_READ:
  case expr::TERM_RECORD_READ:
    return get_lvalue_class(d_tm.term_of(lvalue)[0]);
    break;
  case expr::VARIABLE:
    return get_variable_class(lvalue);
    break;
  default:
    throw parser_exception("not an lvalue");
  }
}

void module::load_variables_into(symbol_table& table) const {
  // We also copy any duplicates
  table.load_full_from(d_variables);
}

void module::insert_with_substitution(term_set& to, const term_set& from, const expr::term_manager::substitution_map& subst) {
  term_set::const_iterator it = from.begin();
  for (; it != from.end(); ++ it) {
    expr::term_ref t = d_tm.substitute(*it, subst);
    to.insert(t);
  }
}

void module::insert_with_substitution(term_to_term_map& to, const term_to_term_map& from, const expr::term_manager::substitution_map& subst) {
  term_to_term_map::const_iterator it = from.begin();
  for (; it != from.end(); ++ it) {
    expr::term_ref t1 = d_tm.substitute(it->first, subst);
    expr::term_ref t2 = d_tm.substitute(it->second, subst);
    to[t1] = t2;
  }
}

void module::insert_with_substitution(variable_class_map& to, const variable_class_map& from, const expr::term_manager::substitution_map& subst) {
  variable_class_map::const_iterator it = from.begin();
  for (; it != from.end(); ++ it) {
    expr::term_ref t = d_tm.substitute(it->first, subst);
    to[t] = it->second;
  }
}

void module::insert_with_substitution(std::vector<expr::term_ref>& to, const std::vector<expr::term_ref>& from, const expr::term_manager::substitution_map& subst) {
  for (size_t i = 0; i < from.size(); ++ i) {
    to.push_back(d_tm.substitute(from[i], subst));
  }
}

void module::insert_with_substitution(module& to_m, const module& from_m, const std::set<std::string>& to_skip, const expr::term_manager::substitution_map& subst, symbol_override allow_override) {
  const symbol_table& from = from_m.d_variables;
  symbol_table& to = to_m.d_variables;

  symbol_table::const_iterator it = from.begin();
  for (; it != from.end(); ++ it) {
    const symbol_table::T_list entries = it->second;

    // Id of the entry
    std::string id = it->first;
    if (to_skip.count(id) > 0) {
      continue;
    }

    // We just take the first one
    expr::term_ref old_entry = entries.front();
    expr::term_ref new_entry = d_tm.substitute(old_entry, subst);

    // Check for duplicates depending on the case
    switch (allow_override) {
    case SYMBOL_OVERRIDE_NO:
      // No duplicates at all
      if (to.has_entry(id)) {
        if (new_entry != to.get_entry(id)) {
          throw parser_exception("redeclaring " + id + " not allowed");
        }
        continue;
      }
      break;
    case SYMBOL_OVERRIDE_YES_EQ:
      if (to.has_entry(id)) {
        // Existing entry
        expr::term_ref current_entry = to.get_entry(id);
        // Check that they are the same
        if (d_tm.type_of(new_entry) != d_tm.type_of(current_entry)) {
          TRACE("sal::module") << "id = " << id << std::endl;
          TRACE("sal::module") << "current = " << current_entry << ", " << d_tm.type_of(current_entry) << " (" << current_entry.index() << ")" << std::endl;
          TRACE("sal::module") << "new = " << new_entry << ", " << d_tm.type_of(new_entry) << " (" << old_entry.index() << ")" << std::endl;
          throw parser_exception("redeclaring " + id + " of a different type is not allowed");
        }
        // Check that they are both parameters or not
        bool is_param1 = from_m.is_parameter(old_entry);
        bool is_param2 = to_m.is_parameter(current_entry);
        if (is_param1 != is_param2) {
          throw parser_exception("redeclaring parameter " + id + " not allowed");
        }
        // Check that they are the same class
        if (!is_param1) {
          variable_class c1 = from_m.get_variable_class(old_entry);
          variable_class c2 = to_m.get_variable_class(current_entry);
          if (c1 != c2) {
            throw parser_exception("redeclaring different class for " + id + " not allowed");
          }
        }
        continue;
      }
      break;
    case SYMBOL_OVERRIDE_YES:
      // Nothing to do, just add to table
      break;
    default:
      assert(false);
    }

    // Done checking, all ok, just add it
    to.add_entry(it->first, new_entry);
  }
}

void module::load_symbols(const module& m, const std::set<std::string>& to_skip, const expr::term_manager::substitution_map& subst, symbol_override allow_override) {

  // Copy over the symbol table (might add duplicates)
  insert_with_substitution(*this, m, to_skip, subst, allow_override);

  // Parameters (there can be duplicates here, no problem)
  insert_with_substitution(d_parameters, m.d_parameters, subst);
  insert_with_substitution(d_vars_parameter, m.d_vars_parameter, subst);

  // Variables sets
  insert_with_substitution(d_vars_input, m.d_vars_input, subst);
  insert_with_substitution(d_vars_output, m.d_vars_output, subst);
  insert_with_substitution(d_vars_local, m.d_vars_local, subst);
  insert_with_substitution(d_vars_global, m.d_vars_global, subst);

  // Variables classes
  insert_with_substitution(d_variable_class, m.d_variable_class, subst);

  // Next variables
  insert_with_substitution(d_variable_next, m.d_variable_next, subst);
}

void module::load_semantics(const module& m, composition_type type, const std::vector<expr::term_ref>& index_vars) {

  expr::term_op quantifier;
  switch (type) {
  case SAL_COMPOSE_ASYNCHRONOUS:
    quantifier = expr::TERM_EXISTS;
    break;
  case SAL_COMPOSE_SYNCHRONOUS:
    quantifier = expr::TERM_FORALL;
    break;
  default:
    assert(false);
    quantifier = expr::TERM_FORALL;
  }

  if (m.d_definitions.size() > 0) {
    expr::term_ref definitions = d_tm.mk_and(m.d_definitions);
    definitions = d_tm.mk_quantifier(quantifier, index_vars, definitions);
    d_definitions.insert(definitions);
  }

  if (m.d_initializations.size() > 0) {
    expr::term_ref initializations = d_tm.mk_and(m.d_initializations);
    initializations = d_tm.mk_quantifier(quantifier, index_vars, initializations);
    d_initializations.insert(initializations);
  }

  if (m.d_transitions.size() > 0) {
    expr::term_ref transitions = d_tm.mk_and(m.d_transitions);
    transitions = d_tm.mk_quantifier(quantifier, index_vars, transitions);
    d_transitions.insert(transitions);
  }

}

void module::load_semantics(const module& m, const expr::term_manager::substitution_map& subst) {
  // Just copy over everything
  insert_with_substitution(d_definitions, m.d_definitions, subst);
  insert_with_substitution(d_initializations, m.d_initializations, subst);
  insert_with_substitution(d_transitions, m.d_transitions, subst);
}

void module::load_semantics(const module& m1, const module& m2, const expr::term_manager::substitution_map& subst_map) {

  // Definitions are kept conjunctive
  insert_with_substitution(d_definitions, m1.d_definitions, subst_map);
  insert_with_substitution(d_definitions, m2.d_definitions, subst_map);

  // Initializations are kept conjunctive
  insert_with_substitution(d_initializations, m1.d_initializations, subst_map);
  insert_with_substitution(d_initializations, m2.d_initializations, subst_map);

  // Transitions are made disjunctive
  // T = (T1 & T2_idle) || (T1_idle & T2)

  expr::term_ref T1 = d_tm.mk_and(m1.d_transitions);
  expr::term_ref T2 = d_tm.mk_and(m2.d_transitions);
  expr::term_ref T1_idle = m1.get_idle();
  expr::term_ref T2_idle = m2.get_idle();

  T1 = d_tm.mk_and(T1, T2_idle);
  T2 = d_tm.mk_and(T2, T1_idle);
  expr::term_ref T = d_tm.mk_or(T1, T2);
  T = d_tm.substitute(T, subst_map);

  assert(d_transitions.size() == 0);
  d_transitions.insert(T);
}

void module::load(const module& m, symbol_override allow_override) {
  expr::term_manager::substitution_map subst;
  std::set<std::string> to_skip;

  // Load the symbols 
  load_symbols(m, to_skip, subst, allow_override);
  // Semantics
  load_semantics(m, subst);
}

void module::load(const module& m, const id_to_lvalue& id_subst, symbol_override allow_override) {
  expr::term_manager::substitution_map term_subst;
  std::set<std::string> to_skip;

  TRACE("sal::module") << "loading with rename:" << std::endl;
  TRACE("sal::module") << "[M = " << m << std::endl << "]" << std::endl;
  TRACE("sal::module") << "[this = " << *this << std::endl << "]" << std::endl;

  // The substitution map is always from id -> (lvalue, lvalue')

  // Create the substitution map
  id_to_lvalue::const_iterator it = id_subst.begin();
  for (; it != id_subst.end(); ++ it) {
    std::string id = it->first;
    // When loading the symbols, we're skipping the renamed one
    to_skip.insert(id);
    // Get the replacement
    const lvalue_info& to = it->second;
    if (!m.has_variable(id)) {
      throw parser_exception(id + " undeclared in module");
    }
    expr::term_ref from = m.get_variable(id);
    // Depending on the override type we check for conflicts
    switch (allow_override) {
    case SYMBOL_OVERRIDE_NO:
      if (has_variable(id)) {
        throw parser_exception("redeclaring " + id + " not allowed.");
      }
      break;
    case SYMBOL_OVERRIDE_YES_EQ: {
      // Check that they are of the same type and class
      if (d_tm.type_of(from) != d_tm.type_of(to.x)) {
        throw parser_exception("redeclaring " + id + " of a different type is not allowed.");
      }
      // Get the classes
      variable_class from_class = m.get_variable_class(from);
      if (from_class != to.var_class) {
        throw parser_exception(d_tm)
            << "redeclaring " << id << " of different classes is not allowed: "
            << from_class << " vs " <<  to.var_class;
      }
      break;
    }
    case SYMBOL_OVERRIDE_YES:
      break;
    default:
      assert(false);
    }

    term_subst[from] = to.x;
    if (m.has_next_variable(from)) {
      // We need from' -> to'
      expr::term_ref from_next = m.get_next_variable(from);
      term_subst[from_next] = to.x_next;
    }
  }

  // Load the symbols
  load_symbols(m, to_skip, term_subst, allow_override);
  // Semantics
  load_semantics(m, term_subst);

  TRACE("sal::module") << "[after renaming *this = " << *this << std::endl << "]" << std::endl;
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

std::ostream& operator << (std::ostream& out, composition_type comp_type) {
  switch (comp_type) {
  case SAL_COMPOSE_SYNCHRONOUS:
    out << "COMPOSE_SYNCHRONOUS";
    break;
  case SAL_COMPOSE_ASYNCHRONOUS:
    out << "COMPOSE_ASYNCHRONOUS";
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
      out << " " << d_parameters[i] << " (" << d_parameters[i].index() << ")";
    }
    out << std::endl;
  }

  if (d_variables.size() > 0) {
    out << "variables";
    symbol_table::const_iterator it = d_variables.begin(), end = d_variables.end();
    for (; it != end; ++ it) {
      expr::term_ref var = it->second.back();
      out << " " << var << " (" << var.index() << ")";
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

bool module::empty() const {
  return d_variables.size() == 0;
}

void module::compose(const module& m_from, composition_type type, const std::vector<expr::term_ref>& index_vars) {

  TRACE("sal::module") << "compose: M as " << type << std::endl;
  TRACE("sal::module") << "[M = " << m_from << std::endl << "]" << std::endl;
  TRACE("sal::module") << "[this = " << *this << std::endl << "]" << std::endl;

  assert(empty());

  // Composition is simple:
  // - add all symbols
  // - quantify the semantics depending on composisiton type

  // First, load the symbols
  expr::term_manager::substitution_map subst;
  std::set<std::string> to_skip;
  load_symbols(m_from, to_skip, subst, SYMBOL_OVERRIDE_NO);
  assert(subst.size() == 0);

  // Add the semantics
  load_semantics(m_from, type, index_vars);

  TRACE("sal::module") << "[|| M = " << *this << std::endl << "]" << std::endl;
}

struct variable_add_info {
  std::string id;
  expr::term_ref v, v_next;
  variable_class v_class;
  variable_add_info(std::string id, expr::term_ref v, expr::term_ref v_next, variable_class v_class)
  : id(id), v(v), v_next(v_next), v_class(v_class) {}
};

void module::finish_symbol_composition(composition_type type, expr::term_manager::substitution_map& subst) {

  // First check that there are not parameters, we can't compose parametrized modules
  if (d_parameters.size() > 0) {
    throw parser_exception("Modules must be instantiated before composition");
  }
  
  /*

    Cases where variables can't be merged
    
     * failure case (sync):

      GLOBAL, GLOBAL:
        Invalid synchronous composition, modules cannot share the global
        variable "x".d

     * failure cases (sync and async)

      GLOBAL, LOCAL:
      INPUT, LOCAL:
      LOCAL, GLOBAL:
      LOCAL, INPUT:
      LOCAL, OUTPUT:
      OUTPUT, LOCAL:
        Invalid module composition, the set of local variables must be disjoint
        from the sets of input, output and global variables in the resultant
        module. The local variable "x" does not satisfy this rule.
      GLOBAL, OUTPUT:
      OUTPUT, GLOBAL:
      OUTPUT, OUTPUT:
        Invalid module composition, the output variable "x" is an output/global
        variable in both modules.
  */

  /*

    The resulting variable classes are

      I = (I1 + I2) - (O + G)
      O = (O1 + O2)
      G = (G1 + G2)
      L = (L1 + L2)

  */

  std::vector<std::string> to_remove_from_symbol_table;

  std::vector<variable_add_info> to_add_list;

  symbol_table::const_iterator it = d_variables.begin();
  for (; it != d_variables.end(); ++ it) {
    std::string var_id = it->first;
    const symbol_table::T_list& vars = it->second;
    if (vars.size() > 1) {
      // If there are many LOCAL variables, we just keep them
      symbol_table::T_list::const_iterator e_it = vars.begin();
      bool all_local = true;
      for (; e_it != vars.end(); ++ e_it) {
        expr::term_ref var = *e_it;
        if (get_variable_class(var) != SAL_VARIABLE_LOCAL) {
          all_local = false;
          break;
        }
      }
      if (!all_local && vars.size() > 2) {
        throw parser_exception("Ambiguous merging: more than 2 variables of the same name '" + var_id + "'");
      }
      if (all_local) {
        // We keep copies of the local variables
        continue;
      }
    }
    if (vars.size() == 2) {
      // We have a merge, check the cases (they are not parameters)
      expr::term_ref v1 = vars.front();
      expr::term_ref v2 = vars.back();
      variable_class v1_class = get_variable_class(v1);
      variable_class v2_class = get_variable_class(v2);

      // Bad cases 
      if (type == SAL_COMPOSE_SYNCHRONOUS && v1_class == SAL_VARIABLE_GLOBAL && v2_class == SAL_VARIABLE_GLOBAL) { 
        throw parser_exception(d_tm) << 
          "Invalid synchronous composition, modules cannot share the global variable" << var_id << ".";
      }      
      if ((v1_class == SAL_VARIABLE_GLOBAL && v2_class == SAL_VARIABLE_LOCAL) ||
          (v1_class == SAL_VARIABLE_INPUT && v2_class == SAL_VARIABLE_LOCAL) ||
          (v1_class == SAL_VARIABLE_LOCAL && v2_class == SAL_VARIABLE_GLOBAL) ||
          (v1_class == SAL_VARIABLE_LOCAL && v2_class == SAL_VARIABLE_INPUT) ||
          (v1_class == SAL_VARIABLE_LOCAL && v2_class == SAL_VARIABLE_OUTPUT) ||
          (v1_class == SAL_VARIABLE_OUTPUT && v2_class == SAL_VARIABLE_LOCAL)) {
        throw parser_exception(d_tm) <<
          "Invalid module composition, the set of local variables must be disjoint "
          "from the sets of input, output and global variables in the resultant "
          "module. The local variable " << var_id << " does not satisfy this rule.";
      }
      if ((v1_class == SAL_VARIABLE_GLOBAL && v2_class == SAL_VARIABLE_OUTPUT) ||
          (v1_class == SAL_VARIABLE_OUTPUT && v2_class == SAL_VARIABLE_GLOBAL) ||
          (v1_class == SAL_VARIABLE_OUTPUT && v2_class == SAL_VARIABLE_OUTPUT)) {
        throw parser_exception(d_tm) <<
          "Invalid module composition, the output variable " << var_id << " is an "
          "output/global variable in both modules.";
      }

      // Resulting type
      variable_class v_class;

      // Remove any global/output variables from the inputs
      if (v1_class == SAL_VARIABLE_INPUT && v2_class == SAL_VARIABLE_OUTPUT) {
        // becomes output
        v_class = SAL_VARIABLE_OUTPUT;
      } else if (v1_class == SAL_VARIABLE_INPUT && v2_class == SAL_VARIABLE_GLOBAL) {
        // becomes global
        v_class = SAL_VARIABLE_GLOBAL;
      } else if (v2_class == SAL_VARIABLE_INPUT && v1_class == SAL_VARIABLE_OUTPUT) {
        // becomes output
        v_class = SAL_VARIABLE_OUTPUT;
      } else if (v2_class == SAL_VARIABLE_INPUT && v1_class == SAL_VARIABLE_GLOBAL) {
        // becomes global
        v_class = SAL_VARIABLE_GLOBAL;
      } else {
        assert(v1_class == v2_class);
        v_class = v1_class;
      }

      // Create a replacement variable and add to substitution map
      expr::term_ref v1_type = d_tm.type_of(v1);
      expr::term_ref v2_type = d_tm.type_of(v2);

      expr::term_ref v_type;
      try {
        v_type = d_tm.mk_intersection_type(v1_type, v2_type);
      } catch (exception& e) {
        // Can't merge variables
        throw parser_exception("Error merging instances of '" + var_id + "': " + e.get_message());
      }

      expr::term_ref v = d_tm.mk_variable(var_id, v_type);

      // Delete both v1 and v2, add v to v_class
      assert(subst.find(v1) == subst.end());
      assert(subst.find(v2) == subst.end());
      subst[v1] = v;
      subst[v2] = v;
      expr::term_ref v_next;
      bool has_next = (has_next_variable(v1) || has_next_variable(v2));
      if (has_next) {
        v_next = d_tm.mk_variable(var_id + "'", v_type);
        if (has_next_variable(v1)) {
          expr::term_ref v1_next = get_next_variable(v1);
          subst[v1_next] = v_next;
        }
        if (has_next_variable(v2)) {
          expr::term_ref v2_next = get_next_variable(v2);
          subst[v2_next] = v_next;
        }
      }
      remove_variable(v1, v1_class);
      remove_variable(v2, v2_class);

      to_remove_from_symbol_table.push_back(var_id);
      to_add_list.push_back(variable_add_info(var_id, v, v_next, v_class));
    }
  }

  // Remove from symbol table
  for (size_t i = 0; i < to_remove_from_symbol_table.size(); ++ i) {
    d_variables.erase_entry(to_remove_from_symbol_table[i]);
  }

  // Add the new variables
  for (size_t i = 0; i < to_add_list.size(); ++ i) {
    const variable_add_info& a = to_add_list[i];
    add_variable(a.id, a.v, a.v_class, a.v_next);
  }
}

module::ref module::compose(const module& other, composition_type type) {

  TRACE("sal::module") << "compose: M1, M2 as " << type << std::endl;
  TRACE("sal::module") << "[M1 = " << *this << std::endl << "]" << std::endl;
  TRACE("sal::module") << "[M2 = " << other << std::endl << "]" << std::endl;

  assert(d_variables.size() > 0);
  assert(other.d_variables.size() > 0);

  // Composition is simple:
  // - create a new module m
  // - load m1 into m
  // - load m2 into m

  module::ref result = new module(d_tm);
  
  // First, load the symbols 
  expr::term_manager::substitution_map subst;
  std::set<std::string> to_skip;
  result->load_symbols(*this, to_skip, subst, SYMBOL_OVERRIDE_NO);
  result->load_symbols(other, to_skip, subst, SYMBOL_OVERRIDE_YES);
  // Allow duplicates above, settle the duplicates
  result->finish_symbol_composition(type, subst);

  // Now, depending on the composition type, add the other stuff
  switch (type) {
  case SAL_COMPOSE_SYNCHRONOUS:
    // We move at the same time, so just add the other stuff
    result->load_semantics(*this, subst);
    result->load_semantics(other, subst);
    break;
  case SAL_COMPOSE_ASYNCHRONOUS:
    // Disjunctive semantics
    result->load_semantics(*this, other, subst);
    break;
  default:
    assert(false);
  }

  TRACE("sal::module") << "[M2 || M2 = " << *result << std::endl << "]" << std::endl;

  return result;
}

const module::symbol_table& module::get_symbol_table() const {
  return d_variables;
}

}
}
}


