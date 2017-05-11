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

#include "parser/sal/sal_context.h"
#include "parser/parser.h"

#include "utils/trace.h"

#include "command/sequence.h"
#include "command/declare_state_type.h"
#include "command/define_states.h"
#include "command/define_transition.h"
#include "command/define_transition_system.h"
#include "command/query.h"

#include "system/state_type.h"

#include <iostream>
#include <sstream>

namespace sally {
namespace parser {
namespace sal {

context::context(expr::term_manager& tm, std::string name)
: d_tm(tm)
, d_name(name)
, d_parameters("parameters")
, d_modules("modules")
{
}

void context::add_parameter(std::string name, expr::term_ref var) {
  if (d_parameters.has_entry(name)) {
    throw parser_exception(name + " already declared");
  }
  d_parameters.add_entry(name, var);
}

void context::add_module(std::string name, sal::module::ref m) {
  if (d_modules.has_entry(name)) {
    throw parser_exception(name + " already declared");
  }
  d_modules.add_entry(name, m);
}

void context::add_assertion(std::string id, assertion_form form, sal::module::ref m, expr::term_ref a) {
  d_assertions.push_back(assertion(id, form, m, a));
}

void context::process_module(module::ref m, cmd::sequence* seq) {
  TRACE("parser::sal") << "context::to_sally_commands(): adding " << m->get_name() << std::endl;

  // State type name
  std::stringstream st_name_ss;
  st_name_ss << m->get_name() << "_state_type";
  std::string st_name = st_name_ss.str();

  typedef std::vector<expr::term_ref> term_ref_vec;
  typedef std::vector<std::string> string_vec;

  // Collect all the variable information
  string_vec state_var_names, input_var_names, param_var_names;
  term_ref_vec state_var_types, input_var_types, param_var_types;
  term_ref_vec state_vars, input_vars, param_vars;

  // Add regular variables to the state type information
  const module::symbol_table& m_symbols = m->get_symbol_table();
  module::symbol_table::const_iterator m_symbols_it = m_symbols.begin();
  for (; m_symbols_it != m_symbols.end(); ++ m_symbols_it) {
    std::string id = m_symbols_it->first;
    const module::symbol_table::T_list& vars = m_symbols_it->second;
    module::symbol_table::T_list::const_iterator it_vars = vars.begin();
    for (size_t i = 0; it_vars != vars.end(); ++ it_vars, ++ i) {
      expr::term_ref var = *it_vars;
      expr::term_ref var_type = d_tm.type_of(var);
      std::string var_name = id;
      if (vars.size() > 1) {
        // In case of duplicates (say for local variables), index them
        std::stringstream ss;
        ss << id << "!" << i;
        var_name = ss.str();
      }
      variable_class var_class = m->get_variable_class(var);
      switch (var_class) {
        case SAL_VARIABLE_GLOBAL:
        case SAL_VARIABLE_LOCAL:
        case SAL_VARIABLE_OUTPUT:
        state_var_names.push_back(var_name);
        state_var_types.push_back(var_type);
        state_vars.push_back(var);
        break;
        case SAL_VARIABLE_INPUT:
        input_var_names.push_back(var_name);
        input_var_types.push_back(var_type);
        input_vars.push_back(var);
        break;
      }
    }
  }

  // Add the context parameters to the state type information
  utils::symbol_table<expr::term_ref>::const_iterator params_it = d_parameters.begin();
  for (; params_it != d_parameters.end(); ++ params_it) {
    std::string var_name = params_it->first;
    expr::term_ref var = params_it->second.front();
    expr::term_ref var_type = d_tm.type_of(var);
    param_var_names.push_back(var_name);
    param_var_types.push_back(var_type);
    param_vars.push_back(var);
  }

  // Create the state part variables
  expr::term_ref state = d_tm.mk_struct_type(state_var_names, state_var_types);
  expr::term_ref input = d_tm.mk_struct_type(input_var_names, input_var_types);
  expr::term_ref params = d_tm.mk_struct_type(param_var_names, param_var_types);

  // Create the state type
  system::state_type* st = new system::state_type(st_name, d_tm, state, input, params);
  assert(d_state_type.find(m) == d_state_type.end());
  d_state_type[m] = st;
  TRACE("parser::sal") << "st: " << *st << std::endl;

  // Add command to the sequence
  seq->push_back(new cmd::declare_state_type(st_name, st));

  // Make a renaming from SAL variables to Sally state-type variables
  expr::term_manager::substitution_map SAL_to_Sally_subst;

  // DJ: extra braces to not confuse the variables

  {
    const term_ref_vec& st_current_vars = st->get_variables(system::state_type::STATE_CURRENT);
    for (size_t i = 0; i < st_current_vars.size(); ++ i) {
      expr::term_ref sally_var = st_current_vars[i];
      expr::term_ref SAL_var = state_vars[i];
      assert(SAL_to_Sally_subst.find(SAL_var) == SAL_to_Sally_subst.end());
      SAL_to_Sally_subst[SAL_var] = sally_var;
    }
  }

  {
    const term_ref_vec& st_input_vars = st->get_variables(system::state_type::STATE_INPUT);
    for (size_t i = 0; i < st_input_vars.size(); ++ i) {
      expr::term_ref sally_var = st_input_vars[i];
      expr::term_ref SAL_var = input_vars[i];
      assert(SAL_to_Sally_subst.find(SAL_var) == SAL_to_Sally_subst.end());
      SAL_to_Sally_subst[SAL_var] = sally_var;
    }
  }

  {
    const term_ref_vec& st_next_vars = st->get_variables(system::state_type::STATE_NEXT);
    for (size_t i = 0; i < st_next_vars.size(); ++ i) {
      expr::term_ref sally_var = st_next_vars[i];
      expr::term_ref SAL_var = m->get_next_variable(state_vars[i]);
      assert(SAL_to_Sally_subst.find(SAL_var) == SAL_to_Sally_subst.end());
      SAL_to_Sally_subst[SAL_var] = sally_var;
    }
  }

  {
    const term_ref_vec& st_param_vars = st->get_variables(system::state_type::STATE_PARAM);
    for (size_t i = 0; i < st_param_vars.size(); ++ i) {
      expr::term_ref sally_var = st_param_vars[i];
      expr::term_ref SAL_var = param_vars[i];
      SAL_to_Sally_subst[SAL_var] = sally_var;
    }
  }

  // Initializations
  const module::term_set& init = m->get_initializations();
  expr::term_ref init_formula = d_tm.mk_and(init);
  init_formula = d_tm.substitute(init_formula, SAL_to_Sally_subst);
  TRACE("parser::sal") << "init_formula: " << init_formula << std::endl;

  // Definitions
  const module::term_set& def = m->get_definitions();
  expr::term_ref def_formula = d_tm.mk_and(def);
  def_formula = d_tm.substitute(def_formula, SAL_to_Sally_subst);
  expr::term_ref def_formula_next = st->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, def_formula);
  TRACE("parser::sal") << "def_formula: " << def_formula << std::endl;
  TRACE("parser::sal") << "def_formula_next: " << def_formula_next << std::endl;

  // Transitions
  const module::term_set& tran = m->get_transitions();
  expr::term_ref tran_formula = d_tm.mk_and(tran);
  tran_formula = d_tm.substitute(tran_formula, SAL_to_Sally_subst);
  TRACE("parser::sal") << "tran_formula_next: " << tran_formula << std::endl;

  // Initial states are init & def
  std::stringstream init_name_ss;
  init_name_ss << m->get_name() << "_init";
  std::string init_name = init_name_ss.str();
  expr::term_ref init_all = d_tm.mk_and(init_formula, def_formula);
  system::state_formula* init_sf = new system::state_formula(d_tm, st, init_all);
  // seq->push_back(new cmd::define_states(init_name, init_sf));

  // Transition is tran & def & def'
  std::stringstream tran_name_ss;
  tran_name_ss << m->get_name() << "_tran";
  std::string tran_name = tran_name_ss.str();
  expr::term_ref tran_all = d_tm.mk_and(tran_formula, def_formula, def_formula_next);
  system::transition_formula* tran_tf = new system::transition_formula(d_tm, st, tran_all);
  // seq->push_back(new cmd::define_transition(tran_name, tran_tf));

  // Define the system
  system::transition_system* system = new system::transition_system(st, init_sf, tran_tf);
  seq->push_back(new cmd::define_transition_system(m->get_name(), system));

  // Remember the substitution
  d_SAL_to_Sally_subst[m].swap(SAL_to_Sally_subst);
}

void context::process_assertion(const system::context& sally_context, const assertion& a, cmd::sequence* seq) {
  TRACE("parser::sal") << "context::to_sally_commands(): adding assertion " << a.form << std::endl;

  // The module
  sal::module::ref m = a.m;

  // The substitution of the model
  module_to_subst_map::const_iterator find_subst = d_SAL_to_Sally_subst.find(m);
  assert(find_subst != d_SAL_to_Sally_subst.end());

  // State type of the module
  module_to_state_type_map::const_iterator find_st = d_state_type.find(m);
  const system::state_type* m_st = find_st->second;

  // Generate the query formula
  expr::term_ref query_formula = d_tm.substitute(a.formula, find_subst->second);
  system::state_formula* query_sf = new system::state_formula(d_tm, m_st, query_formula);

  // The query comand
  cmd::command* query_cmd = new cmd::query(sally_context, m->get_name(), query_sf);
  seq->push_back(query_cmd);
}

cmd::command* context::to_sally_commands(const system::context& sally_context) {
  TRACE("parser::sal") << "context::add_to_sally()" << std::endl;

  cmd::sequence* seq = new cmd::sequence();

  // Get all the modules from the assertions
  std::set<sal::module::ref> modules;
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    const assertion& a = d_assertions[i];
    modules.insert(a.m);
  }

  // Define all the modules
  TRACE("parser::sal") << "context:to_sally_commands(): adding modules" << std::endl;
  std::set<sal::module::ref>::const_iterator it = modules.begin();
  for (; it != modules.end(); ++ it) {
    process_module(*it, seq);
  }

  // Make the commands from assertions
  TRACE("parser::sal") << "context::to_sally_commands(): creating commands" << std::endl;
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    const assertion& a = d_assertions[i];
    process_assertion(sally_context, a, seq);
  }

  // Clear the caches
  d_SAL_to_Sally_subst.clear();
  d_state_type.clear();

  return seq;
}

std::ostream& operator << (std::ostream& out, assertion_form form) {

  switch (form) {
  case SAL_OBLIGATION: out << "OBLIGATION"; break;
  case SAL_CLAIM: out << "CLAIM"; break;
  case SAL_LEMMA: out << "LEMMA"; break;
  case SAL_THEOREM: out << "THEOREM"; break;
  };

  return out;
}

}
}
}



