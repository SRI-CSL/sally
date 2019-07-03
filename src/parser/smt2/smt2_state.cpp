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

#include "parser/smt2/smt2_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "system/transition_system.h"

#include "command/declare_state_type.h"
#include "command/define_transition_system.h"
#include "command/sequence.h"
#include "command/query.h"

#include <cassert>
#include <iostream>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

smt2_state::smt2_state(const system::context& context)
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

string smt2_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref smt2_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref smt2_state::get_bitvector_type(size_t size) const {
  return tm().bitvector_type(size);
}

term_ref smt2_state::get_variable(std::string id) const {
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

void smt2_state::set_variable(std::string id, expr::term_ref t) {
  d_variables.add_entry(id, t);
}

void smt2_state::declare_variable(std::string id, expr::term_ref type) {
  expr::term_ref var = tm().mk_variable(id, type);
  d_variables.add_entry(id, var);
  d_variable_ids.push_back(id);
  d_variable_terms.push_back(var);
  d_variable_types.push_back(type);
}

void smt2_state::push_scope() {
  d_variables.push_scope();
}

void smt2_state::pop_scope() {
  d_variables.pop_scope();
}

bool smt2_state::is_declared(std::string id, smt2_object type) const {
  switch (type) {
  case SMT2_VARIABLE:
    return d_variables.has_entry(id);
    break;
  case SMT2_TYPE:
    return d_types.has_entry(id);
    break;
  case SMT2_OBJECT_LAST:
    // Always no op
    return false;
  default:
    assert(false);
  }

  return false;
}

void smt2_state::ensure_declared(std::string id, smt2_object type, bool declared) const {
  if (declared != is_declared(id, type)) {
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
expr::term_ref smt2_state::mk_cond(const std::vector<expr::term_ref>& children) {
  assert(children.size() & 1);
  assert(children.size() >= 3);

  expr::term_ref result = children.back();
  for (int i = children.size() - 3; i >= 0; i -= 2) {
    result = tm().mk_term(expr::TERM_ITE, children[i], children[i+1], result);
  }
  return result;
}

cmd::command* smt2_state::mk_smt2_system() {

  cmd::sequence* result = new cmd::sequence();

  std::vector<std::string> input_names;
  std::vector<expr::term_ref> input_types;

  // Make the state type
  expr::term_ref input_type_ref = tm().mk_struct_type(input_names, input_types);
  expr::term_ref state_type_ref = tm().mk_struct_type(d_variable_ids, d_variable_types);
  system::state_type* state_type = new system::state_type("vars", tm(), state_type_ref, input_type_ref);

  // Make the substitution from SMT formula to state variables
  expr::term_manager::substitution_map subst;
  const std::vector<expr::term_ref>& state_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    subst[d_variable_terms[i]] = state_vars[i];
  }

  // Declare the type
  cmd::command* type_declare = new cmd::declare_state_type("type", state_type);
  result->push_back(type_declare);

  // Make the inital state formula
  expr::term_ref initial_states = tm().mk_and(d_assertions);
  initial_states = tm().substitute(initial_states, subst);
  system::state_formula* init_f = new system::state_formula(tm(), state_type, initial_states);

  // Make the transition
  system::transition_formula* transition_f = new system::transition_formula(tm(), state_type, tm().mk_boolean_constant(false));

  // Make the transition system
  system::transition_system* ts = new system::transition_system(state_type, init_f, transition_f);
  cmd::command* ts_define = new cmd::define_transition_system("ts", ts);
  result->push_back(ts_define);

  // Make the property
  system::state_formula* property_f = new system::state_formula(tm(), state_type, tm().mk_boolean_constant(false));
  cmd::command* query = new cmd::query(d_context, "ts", property_f);
  result->push_back(query);

  return result;
}

expr::term_ref smt2_state::mk_rational_constant(std::string number) {

  size_t f = number.find('.');

  if (f != std::string::npos) {
    std::string p = number.substr(0, f);
    std::string q = number.substr(f + 1);
    rational r(p, q);
    return tm().mk_rational_constant(r);
  } else {
    // integer
    rational r(number);
    return tm().mk_rational_constant(r);
  }

}

void smt2_state::assert_command(expr::term_ref f) {
  d_assertions.push_back(f);
}

void smt2_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
  gc_reloc.reloc(d_assertions);
}
