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

#include "parser/btor2/btor2_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include "command/assume.h"
#include "command/declare_state_type.h"
#include "command/define_states.h"
#include "command/define_transition.h"
#include "command/define_transition_system.h"
#include "command/query.h"
#include "command/sequence.h"

#include <cassert>
#include <sstream>
#include <iostream>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

btor2_state::btor2_state(const system::context& context)
: d_context(context)
{
  d_one = expr::term_ref_strong(tm(), tm().mk_bitvector_constant(bitvector(1, 1)));
  d_zero = expr::term_ref_strong(tm(), tm().mk_bitvector_constant(bitvector(1, 0)));
}

string btor2_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

int btor2_state::token_as_int(pANTLR3_COMMON_TOKEN token) {
  return std::stoi(token_text(token));
}

integer btor2_state::token_as_integer(pANTLR3_COMMON_TOKEN token, size_t base) {
  return integer(token_text(token), base);
}

void btor2_state::add_bv_type(size_t index, size_t size)
{
  if (size == 0) {
    throw parser_exception("Bitvector size must be non-negative.");
  }
  // Ensure size
  if (index >= d_nodes.size()) {
    d_nodes.resize((index * 2) + 1);
  }
  // Remember
  d_nodes[index] = tm().bitvector_type(size);
}

expr::term_ref btor2_state::get_type(size_t index) const {
  if (index >= d_nodes.size() || d_nodes[index].is_null()) {
    throw exception("Index not declared yet");
  }
  if (!tm().is_type(d_nodes[index])) {
    throw exception("Node at index is not a type");
  }
  return d_nodes[index];
}

void btor2_state::set_term(size_t index, term_ref term, term_ref type) {
  // Ensure size
  if (index >= d_nodes.size()) {
    d_nodes.resize((index * 2) + 1);
  }
  // Ensure bit-vector
  if (tm().type_of(term) == tm().boolean_type()) {
    term = tm().mk_term(expr::TERM_ITE, term, d_one, d_zero);
  }
  if (tm().get_bitvector_size(term) != tm().get_bitvector_type_size(type)) {
    throw exception("Bitvector sizes don't match.");
  }
  // Remember
  d_nodes[index] = term;
}

expr::term_ref btor2_state::get_term(int index) const {
  size_t i = index >= 0 ? index : -index;
  if (i >= d_nodes.size() || d_nodes[i].is_null()) {
    throw exception("Index not declared yet");
  }
  term_ref result = d_nodes[i];
  if (index >= 0) {
    return result;
  } else {
    if (tm().type_of(result) == tm().boolean_type()) {
      return tm().mk_term(expr::TERM_NOT, result);
    } else {
      return tm().mk_term(expr::TERM_BV_NOT, result);
    }
  }
}

void btor2_state::add_input_var(size_t id, size_t type_id, std::string name) {
  term_ref type = get_type(type_id);
  term_ref term = tm().mk_variable(name, type);
  set_term(id, term, type);
  d_input_vars.push_back(id);
}

void btor2_state::add_state_var(size_t id, size_t type_id, std::string name) {
  term_ref type = get_type(type_id);
  term_ref term = tm().mk_variable(name, type);
  set_term(id, term, type);
  d_state_vars.push_back(id);
}

void btor2_state::add_constant_zero(size_t id, size_t type_id) {
  term_ref type = get_type(type_id);
  size_t width = tm().get_bitvector_type_size(type);
  term_ref term = tm().mk_bitvector_constant(expr::bitvector(width, 0));
  set_term(id, term, type);
}

void btor2_state::add_constant_one(size_t id, size_t type_id) {
  term_ref type = get_type(type_id);
  size_t width = tm().get_bitvector_type_size(type);
  term_ref term = tm().mk_bitvector_constant(expr::bitvector(width, 1));
  set_term(id, term, type);
}

void btor2_state::add_constant_ones(size_t id, size_t type_id) {
  term_ref type = get_type(type_id);
  size_t width = tm().get_bitvector_type_size(type);
  term_ref term = tm().mk_bitvector_constant(expr::bitvector::one(width));
  set_term(id, term, type);
}

void btor2_state::add_constant(size_t id, size_t type_id, const expr::integer i) {
  term_ref type = get_type(type_id);
  size_t width = tm().get_bitvector_type_size(type);
  term_ref term = tm().mk_bitvector_constant(expr::bitvector(width, i));
  set_term(id, term, type);
}

void btor2_state::set_init(size_t id, size_t type_id, size_t var_id, term_ref value) {
  var_to_var_map::const_iterator find = d_init.find(var_id);
  if (find != d_init.end()) {
    throw exception("Init already defined for this variable.");
  }
  term_ref type = get_type(type_id);
  if (tm().is_bitvector_type(value) && tm().get_bitvector_size(value) != tm().get_bitvector_type_size(type)) {
    throw exception("Bitvector sizes don't match");
  }
  d_init[var_id] = id;
  set_term(id, value, type);
}

void btor2_state::set_next(size_t id, size_t type_id, size_t var_id, term_ref value) {
  var_to_var_map::const_iterator find = d_next.find(var_id);
  if (find != d_next.end()) {
    throw exception("Next already defined for this variable.");
  }
  term_ref type = get_type(type_id);
  if (tm().is_bitvector_type(value) && tm().get_bitvector_size(value) != tm().get_bitvector_type_size(type)) {
    throw exception("Bitvector sizes don't match");
  }
  d_next[var_id] = id;
  set_term(id, value, type);
}

static size_t power_log(size_t size) {
  assert(size > 0);
  size_t log = 0;
  while ((size & 1) == 0) {
    size >>= 1;
    log ++;
  }
  if (size != 1) {
    throw parser_exception("Bitvector size must be a power of two.");
  }
  return log;
}

void btor2_state::add_unary_term(size_t id, term_op op, size_t type_id, term_ref t) {
  term_ref type = get_type(type_id);
  term_ref term = tm().mk_term(op, t);
  set_term(id, term, type);
}

void btor2_state::add_binary_term(size_t id, term_op op, size_t type_id, term_ref t1, term_ref t2) {
  term_ref term;
  term_ref type = get_type(type_id);
  size_t bv_type_size = tm().get_bitvector_type_size(type);

  // FIXME: why treat shifts like this?
  switch (op) {
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR: {
    // Special treatment for shifts, size is a power of two
    size_t size_log = power_log(bv_type_size);
    // Padding the shift amount to size
    bitvector bv(bv_type_size - size_log);
    term_ref padding = tm().mk_bitvector_constant(bv);
    // Extend the shift factor to the size
    t2 = tm().mk_term(expr::TERM_BV_CONCAT, padding, t2);
    // Make the term
    term = tm().mk_term(op, t1, t2);
    break;
  }
  case TERM_IMPLIES: {
    size_t t1_width = tm().get_bitvector_size(t1);
    size_t t2_width = tm().get_bitvector_size(t2);
    if (t1_width != 1 || t2_width != 1) {
      throw parser_exception("implies terms can only be of size 1.");
    }
    term = tm().mk_term(op, tm().mk_term(TERM_EQ, t1, d_one), 
                            tm().mk_term(TERM_EQ, t2, d_one));
    break;
  }
  default:
    // Default, we just make it
    term = tm().mk_term(op, t1, t2);
  }

  // Set the data
  set_term(id, term, type);
}

void btor2_state::add_ite(size_t id, size_t type_id, expr::term_ref c, expr::term_ref t_true, expr::term_ref t_false) {
  term_ref type = get_type(type_id);
  term_ref eq = tm().mk_term(expr::TERM_EQ, c, d_one);
  term_ref term = tm().mk_term(expr::TERM_ITE, eq, t_true, t_false);
  set_term(id, term, type);
}

void btor2_state::add_uext(size_t id, size_t type_id, expr::term_ref t, size_t amt) {
  term_ref type = get_type(type_id);
  size_t width = tm().get_bitvector_type_size(type);
  if (amt > width) {
    throw parser_exception("Bitvector size must be greater than the extension amount.");
  }
  term_ref term = tm().mk_bitvector_uext(t, amt);
  set_term(id, term, type);
}

void btor2_state::add_sext(size_t id, size_t type_id, expr::term_ref t, size_t amt) {
  term_ref type = get_type(type_id);
  term_ref term = tm().mk_bitvector_sgn_extend(t, bitvector_sgn_extend(amt));
  set_term(id, term, type);
}

void btor2_state::add_slice(size_t id, size_t type_id, term_ref t, size_t high, size_t low) {
  term_ref type = get_type(type_id);
  term_ref term = tm().mk_bitvector_extract(t, bitvector_extract(high, low));
  set_term(id, term, type);
}

void btor2_state::add_constraint(size_t id, term_ref term) {
  term_ref type = tm().type_of(term);
  if (tm().get_bitvector_type_size(type) != 1) {
    throw parser_exception("'contraint' terms can only be of size 1.");
  }
  d_constraints.push_back(expr::term_ref_strong(tm(), term));
  set_term(id, term, type);
}

void btor2_state::add_bad(size_t id, term_ref term) {
  term_ref type = tm().type_of(term);
  if (tm().get_bitvector_type_size(type) != 1) {
    throw parser_exception("'bad' terms can only be of size 1.");
  }
  d_bad.push_back(expr::term_ref_strong(tm(), term));
  set_term(id, term, type);
}

cmd::command* btor2_state::finalize() const {
  // Create the state type
  std::vector<std::string> input_names, state_names;
  std::vector<term_ref> input_types, state_types;
  // Construct the state type
  for (size_t i = 0; i < d_input_vars.size(); ++ i) {
    term_ref var_ref = get_term(d_input_vars[i]);
    const term& var = tm().term_of(var_ref);
    input_names.push_back(tm().get_variable_name(var));
    input_types.push_back(tm().type_of(var));
  }
  term_ref input_type_ref = tm().mk_struct_type(input_names, input_types);

  for (size_t i = 0; i < d_state_vars.size(); ++ i) {
    term_ref var_ref = get_term(d_state_vars[i]);
    const term& var = tm().term_of(var_ref);
    state_names.push_back(tm().get_variable_name(var));
    state_types.push_back(tm().type_of(var));
  }
  term_ref state_type_ref = tm().mk_struct_type(state_names, state_types);

  system::state_type* state_type = new system::state_type("state_type", tm(), state_type_ref, input_type_ref);
  cmd::command* state_type_declare = new cmd::declare_state_type("state_type", state_type);

  // Get the state variables
  const std::vector<term_ref>& input_vars = state_type->get_variables(system::state_type::STATE_INPUT);
  const std::vector<term_ref>& current_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<term_ref>& next_vars = state_type->get_variables(system::state_type::STATE_NEXT);

  // Create the conversion table from btor vars to input, state, and next vars
  term_manager::substitution_map btor_to_state_var;
  for (size_t i = 0; i < d_input_vars.size(); ++ i) {
    term_ref btor_var = get_term(d_input_vars[i]);
    term_ref state_var = input_vars[i];
    btor_to_state_var[btor_var] = state_var;
  }
  for (size_t i = 0; i < d_state_vars.size(); ++ i) {
    term_ref btor_var = get_term(d_state_vars[i]);
    term_ref state_var = current_vars[i];
    btor_to_state_var[btor_var] = state_var;
  }

  // Initialize the registers (no-next) to zero
  std::vector<term_ref> init_children;
  for (size_t i = 0; i < d_state_vars.size(); ++ i) {
    size_t btor_var_index = d_state_vars[i];
    term_ref state_var = current_vars[i];
    var_to_var_map::const_iterator find = d_init.find(btor_var_index);
    if (find == d_init.end()) { continue; } 
    term_ref init_value = get_term(find->second);
    term_ref eq = tm().mk_term(TERM_EQ, state_var, init_value);
    init_children.push_back(eq);
  }
  term_ref init = tm().mk_and(init_children);
  system::state_formula* init_formula = new system::state_formula(tm(), state_type, init);

  // Define the transition relation
  std::vector<term_ref> transition_children;
  for (size_t i = 0; i < d_state_vars.size(); ++ i) {
    size_t btor_var_index = d_state_vars[i];
    term_ref next_var = next_vars[i];
    var_to_var_map::const_iterator find = d_next.find(btor_var_index);
    if (find == d_next.end()) { continue; } 
    term_ref next_value = get_term(find->second);
    term_ref eq = tm().mk_term(TERM_EQ, next_var, next_value);
    transition_children.push_back(eq);
  }
  term_ref transition = tm().mk_and(transition_children);
  transition = tm().substitute_and_cache(transition, btor_to_state_var);
  system::transition_formula* transition_formula = new system::transition_formula(tm(), state_type, transition);

  // Define any invariants
  std::vector<term_ref> constraint_children;
  for (size_t i = 0; i < d_constraints.size(); ++ i) {
    term_ref constraint = d_constraints[i];
    if (tm().type_of(constraint) != tm().boolean_type()) {
      constraint = tm().mk_term(expr::TERM_EQ, constraint, d_one);
    }
    constraint_children.push_back(constraint);
  }
  term_ref invar = tm().mk_and(constraint_children);
  invar = tm().substitute_and_cache(invar, btor_to_state_var);
  system::state_formula* invar_formula = new system::state_formula(tm(), state_type, invar);

  // Define the transition system
  system::transition_system* transition_system = new system::transition_system(state_type, init_formula, transition_formula, invar_formula);
  cmd::command* transition_system_define = new cmd::define_transition_system("Sys", transition_system);

  // Query
  std::vector<term_ref> bad_children;
  for (size_t i = 0; i < d_bad.size(); ++ i) {
    term_ref bad = tm().substitute_and_cache(d_bad[i], btor_to_state_var);
    if (tm().type_of(bad) != tm().boolean_type()) {
      bad = tm().mk_term(expr::TERM_EQ, bad, d_one);
    }
    bad_children.push_back(bad);
  }
  term_ref property = tm().mk_or(bad_children);
  property = tm().mk_term(TERM_NOT, property);
  system::state_formula* property_formula = new system::state_formula(tm(), state_type, property);
  cmd::command* query = new cmd::query(ctx(), "Sys", property_formula);

  // Make the final command
  cmd::sequence* full_command = new cmd::sequence();
  full_command->push_back(state_type_declare);
  full_command->push_back(transition_system_define);
  full_command->push_back(query);

  return full_command;
}


void btor2_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_nodes);
  gc_reloc.reloc(d_bad);
  gc_reloc.reloc(d_one);
  gc_reloc.reloc(d_zero);
}
