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

#include "parser/btor/btor_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include <cassert>
#include <sstream>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

btor_state::btor_state(const system::context& context)
: d_context(context)
{
  d_one = expr::term_ref_strong(tm(), tm().mk_bitvector_constant(bitvector(1, 1)));
  d_zero = expr::term_ref_strong(tm(), tm().mk_bitvector_constant(bitvector(1, 0)));
}

string btor_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

int btor_state::token_as_int(pANTLR3_COMMON_TOKEN token) {
  int value;
  std::stringstream ss;
  ss << token_text(token);
  ss >> value;
  return value;
}

integer btor_state::token_as_integer(pANTLR3_COMMON_TOKEN token, size_t base) {
  return integer(token_text(token), base);
}

void btor_state::set_term(size_t index, term_ref term, size_t size) {
  // Ensure size
  if (index >= d_terms.size()) {
    d_terms.resize(index + 1);
  }
  // Ensure bit-vector
  if (tm().type_of(term) == tm().boolean_type()) {
    term = tm().mk_term(expr::TERM_ITE, term, d_one, d_zero);
  }
  // Ensure the right size
  term_ref term_type = tm().type_of(term);
  if (tm().get_bitvector_type_size(term_type) != size) {
    throw exception("Bitvector sizes don't match.");
  }
  // Remember
  d_terms[index] = term;
}

expr::term_ref btor_state::get_term(int index) const {
  size_t i = index >= 0 ? index : -index;
  if (i >= d_terms.size() || d_terms[i].is_null()) {
    throw exception("Index not declared yet");
  }
  term_ref result = d_terms[i];
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

expr::term_ref btor_state::get_next(size_t index) const {
  var_to_var_map::const_iterator find = d_variables_next.find(index);
  return get_term(find->second);
}


void btor_state::add_variable(size_t id, size_t size, std::string name) {
  term_ref type = tm().bitvector_type(size);
  term_ref term = tm().mk_variable(name, type);
  set_term(id, term, size);
  d_variables.push_back(id);
}

void btor_state::add_next_variable(size_t id, size_t size, size_t var_id, term_ref value) {
  var_to_var_map::const_iterator find = d_variables_next.find(var_id);
  if (find != d_variables_next.end()) {
    throw exception("Next already defined for this variable.");
  }
  if (tm().get_bitvector_type_size(tm().type_of(value)) != size) {
    throw exception("Bitvector sizes don't match");
  }
  d_variables_next[var_id] = id;
  set_term(id, value, size);
}

void btor_state::add_constant(size_t id, size_t size, const bitvector& bv) {
  term_ref term = tm().mk_bitvector_constant(bv);
  set_term(id, term, size);
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

void btor_state::add_term(size_t id, term_op op, size_t size, term_ref t1, term_ref t2) {

  if (size == 0) {
    throw parser_exception("Bitvector size must be non-negative.");
  }

  term_ref term;

  switch (op) {
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR: {
    // Special treatment for shifts, size is a power of two
    size_t size_log = power_log(size);
    // Padding the shift amount to size
    bitvector bv(size - size_log);
    term_ref padding = tm().mk_bitvector_constant(bv);
    // Extend the shift factor to the size
    t2 = tm().mk_term(expr::TERM_BV_CONCAT, padding, t2);
    // Make the term
    term = tm().mk_term(op, t1, t2);
    break;
  }
  default:
    // Default, we just make it
    term = tm().mk_term(op, t1, t2);
  }

  // Set the data
  set_term(id, term, size);
}

void btor_state::add_ite(size_t id, size_t size, expr::term_ref c, expr::term_ref t_true, expr::term_ref t_false) {
  term_ref eq = tm().mk_term(expr::TERM_EQ, c, d_one);
  term_ref term = tm().mk_term(expr::TERM_ITE, eq, t_true, t_false);
  set_term(id, term, size);
}

void btor_state::add_slice(size_t id, size_t size, term_ref t, size_t high, size_t low) {
  term_ref term = tm().mk_bitvector_extract(t, bitvector_extract(high, low));
  set_term(id, term, size);
}

void btor_state::add_root(size_t id, size_t size, term_ref term) {
  if (size != 1) {
    throw parser_exception("Roots can only be of size 1.");
  }
  d_roots.push_back(expr::term_ref_strong(tm(), term));
  set_term(id, term, size);
}

bool btor_state::is_register(size_t index) const {
  return d_variables_next.find(index) != d_variables_next.end();
}

command* btor_state::finalize() const {

  // Create the state type
  std::vector<std::string> names;
  std::vector<term_ref> types;
  // No inputs, just empty struct
  term_ref input_type_ref = tm().mk_struct_type(names, types);
  // Construct the state type
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    term_ref var_ref = get_term(d_variables[i]);
    const term& var = tm().term_of(var_ref);
    names.push_back(tm().get_variable_name(var));
    types.push_back(tm().type_of(var));
  }
  term_ref state_type_ref = tm().mk_struct_type(names, types);
  system::state_type* state_type = new system::state_type("state_type", tm(), state_type_ref, input_type_ref);
  command* state_type_declare = new declare_state_type_command("state_type", state_type);

  // Get the state variables
  const std::vector<term_ref>& current_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<term_ref>& next_vars = state_type->get_variables(system::state_type::STATE_NEXT);

  // Create the conversion table from btor vars to state and next vars
  term_manager::substitution_map btor_to_state_var;
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    term_ref btor_var = get_term(d_variables[i]);
    term_ref state_var = current_vars[i];
    btor_to_state_var[btor_var] = state_var;
  }

  // Initialize the registers (no-next) to zero
  std::vector<term_ref> init_children;
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    if (is_register(d_variables[i])) {
      term_ref state_var = current_vars[i];
      size_t size = tm().get_bitvector_size(state_var);
      term_ref zero = tm().mk_bitvector_constant(bitvector(size));
      term_ref eq = tm().mk_term(TERM_EQ, state_var, zero);
      init_children.push_back(eq);
    }
  }
  term_ref init = tm().mk_and(init_children);
  system::state_formula* init_formula = new system::state_formula(tm(), state_type, init);

  // Define the transition relation
  std::vector<term_ref> transition_children;
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    size_t btor_var_index = d_variables[i];
    if (is_register(btor_var_index)) {
      term_ref next_var = next_vars[i];
      term_ref next_value = get_next(btor_var_index);
      term_ref eq = tm().mk_term(TERM_EQ, next_var, next_value);
      transition_children.push_back(eq);
    }
  }
  term_ref transition = tm().mk_and(transition_children);
  transition = tm().substitute_and_cache(transition, btor_to_state_var);
  system::transition_formula* transition_formula = new system::transition_formula(tm(), state_type, transition);

  // Define the transition system
  system::transition_system* transition_system = new system::transition_system(state_type, init_formula, transition_formula);
  command* transition_system_define = new define_transition_system_command("T", transition_system);

  // Query
  std::vector<term_ref> bad_children;
  for (size_t i = 0; i < d_roots.size(); ++ i) {
    term_ref bad = tm().substitute_and_cache(d_roots[i], btor_to_state_var);
    bad_children.push_back(bad);
  }
  term_ref property = tm().mk_or(bad_children);
  property = tm().mk_term(TERM_EQ, property, d_zero);
  system::state_formula* property_formula = new system::state_formula(tm(), state_type, property);
  command* query = new query_command(ctx(), "T", property_formula);

  // Make the final command
  sequence_command* full_command = new sequence_command();
  full_command->push_back(state_type_declare);
  full_command->push_back(transition_system_define);
  full_command->push_back(query);

  return full_command;
}


void btor_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_terms);
  gc_reloc.reloc(d_roots);
  gc_reloc.reloc(d_one);
  gc_reloc.reloc(d_zero);
}
