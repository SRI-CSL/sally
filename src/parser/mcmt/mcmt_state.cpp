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

#include "parser/mcmt/mcmt_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include <cassert>

#include <sstream> 

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

mcmt_state::mcmt_state(const system::context& context)
: d_context(context)
, d_variables("local vars")
, d_types("types")
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.real_type()));
  d_types.add_entry("Bool", term_ref_strong(tm, tm.boolean_type()));
  d_types.add_entry("Int", term_ref_strong(tm, tm.integer_type()));
}

string mcmt_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref mcmt_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref mcmt_state::get_bitvector_type(size_t size) const {
  return tm().bitvector_type(size);
}

term_ref mcmt_state::get_variable(std::string id) const {
  int i = 0;
  lambda_variables_list::const_iterator it = lambda_variables.begin();
  for(; it != lambda_variables.end(); ++ it) {
    i++;
    if(it->first == id) {
      term_ref result = tm().mk_quantified_constant(i, it->second);
      return result;
    }
  }
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

void mcmt_state::set_variable(std::string id, expr::term_ref t) {
  d_variables.add_entry(id, expr::term_ref_strong(tm(), t));
}


system::state_type* mcmt_state::mk_state_type(std::string id,
    const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
    const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types) const
{
  expr::term_ref state_type = tm().mk_struct_type(state_vars, state_types);
  expr::term_ref input_type = tm().mk_struct_type(input_vars, input_types);
  return new system::state_type(id, tm(), state_type, input_type);
}

void mcmt_state::use_state_type(std::string id, system::state_type::var_class var_class, bool use_namespace) {
  const system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void mcmt_state::use_state_type(const system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

  // Use the appropriate namespace
  st->use_namespace();
  if (use_namespace) {
    st->use_namespace(var_class);
  }

  // Declare the variables
  const std::vector<expr::term_ref>& vars = st->get_variables(var_class);
  for (size_t i = 0; i < vars.size(); ++ i) {
    const term& var_term = tm().term_of(vars[i]);
    std::string var_name = tm().get_variable_name(var_term);
    d_variables.add_entry(var_name, expr::term_ref_strong(tm(), vars[i]));
  }

  // Declare all the state formulas of this type
  system::context::id_set::const_iterator it = ctx().state_formulas_begin(st);
  system::context::id_set::const_iterator it_end = ctx().state_formulas_end(st);
  for (; it != it_end; ++ it) {
    const system::state_formula* f = ctx().get_state_formula(*it);
    // Get the term of the formula and transform the variables if going to the next state
    expr::term_ref f_term = f->get_formula();
    if (var_class == system::state_type::STATE_NEXT) {
      f_term = st->change_formula_vars(system::state_type::STATE_CURRENT, var_class, f_term);
    }
    // Get the id and turn it into a state type proper id
    std::string id = st->get_canonical_name(*it, var_class);
    // Add to variable table
    d_variables.add_entry(id, expr::term_ref_strong(tm(), f_term));
  }

  // Pop the namespace
  tm().pop_namespace();
  if (use_namespace) {
    tm().pop_namespace();
  }
}

void mcmt_state::use_state_type_and_transitions(const system::state_type* st) {
  // Use the current state
  use_state_type(st, system::state_type::STATE_CURRENT, lsal_extensions());
  // Use the input variables
  use_state_type(st, system::state_type::STATE_INPUT, no_input_namespace());
  // Use the next state
  use_state_type(st, system::state_type::STATE_NEXT, false);
  // Use all the transition formulas
  system::context::id_set::const_iterator it = ctx().transition_formulas_begin(st);
  system::context::id_set::const_iterator it_end = ctx().transition_formulas_end(st);
  for (; it != it_end; ++ it) {
    const system::transition_formula* f = ctx().get_transition_formula(*it);
    // Add to variable table
    d_variables.add_entry(*it, expr::term_ref_strong(tm(), f->get_formula()));
  }
}

void mcmt_state::push_scope() {
  d_variables.push_scope();
}

void mcmt_state::pop_scope() {
  d_variables.pop_scope();
}

bool mcmt_state::is_declared(std::string id, mcmt_object type) const {
  switch (type) {
  case MCMT_VARIABLE:
    return d_variables.has_entry(id);
    break;
  case MCMT_TYPE:
    return d_types.has_entry(id);
    break;
  case MCMT_STATE_TYPE:
    return d_context.has_state_type(id);
    break;
  case MCMT_STATE_FORMULA:
    return d_context.has_state_formula(id);
    break;
  case MCMT_TRANSITION_FORMULA:
    return d_context.has_transition_formula(id);
    break;
  case MCMT_TRANSITION_SYSTEM:
    return d_context.has_transition_system(id);
    break;
  case MCMT_OBJECT_LAST:
    // Always no op
    return false;
  case MCMT_PROCESS_TYPE:
    return false;
  default:
    assert(false);
  }

  return false;
}

void mcmt_state::ensure_declared(std::string id, mcmt_object type, bool declared) const {
  if (declared != is_declared(id, type)) {
    lambda_variables_list::const_iterator it = lambda_variables.begin();
    for(; it != lambda_variables.end(); ++ it) {
      if (it->first == id) {
	return;
      }
    }
    if (declared) throw parser_exception(id + " not declared");
    else throw parser_exception(id + " already declared");
  }
}

/**
 * Make a condition term:
 * if c[0] then c[1]
 * elif c[2] then c[3]
 * ...
 * else c[2n]
 */
expr::term_ref mcmt_state::mk_cond(const std::vector<expr::term_ref>& children) {
  assert(children.size() & 1);
  assert(children.size() >= 3);

  expr::term_ref result = children.back();
  for (int i = children.size() - 3; i >= 0; i -= 2) {
    result = tm().mk_term(expr::TERM_ITE, children[i], children[i+1], result);
  }
  return result;
}

bool mcmt_state::lsal_extensions() const {
  return ctx().get_options().get_bool("lsal-extensions");
}

bool mcmt_state::no_input_namespace() const {
  return ctx().get_options().get_bool("no-input-namespace");
}

void mcmt_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
}

void mcmt_state::mk_process_type(std::string id) {
  term_manager& tm = d_context.tm();
  d_types.add_entry(id, term_ref_strong(tm, tm.mk_process_type(id)));
}

expr::term_ref mcmt_state::mk_array_type(expr::term_ref from, expr::term_ref to) {
  /* FIXME: not very elegant way to get a unique but reproducible id for the array type */
  std::stringstream ss;
  term_manager& tm = d_context.tm();
  ss << term_ref_strong(tm, from).hash() << "^" << term_ref_strong(tm, to).hash();
  term_ref_strong array = term_ref_strong(tm, tm.mk_array_type(from, to));
  d_types.add_entry(ss.str(), array);
  return array;
}

void mcmt_state::push_lambda(std::string v, expr::term_ref type) {
	lambda_variables.push_front(std::make_pair(v, type));
}

void mcmt_state::pop_lambda() {
	lambda_variables.pop_front();
}
