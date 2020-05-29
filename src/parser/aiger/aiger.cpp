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

#include "aiger.h"

#include <vector>
#include <boost/unordered_map.hpp>

#include "command/assume.h"
#include "command/declare_state_type.h"
#include "command/define_states.h"
#include "command/define_transition.h"
#include "command/define_transition_system.h"
#include "command/query.h"
#include "command/sequence.h"

extern "C"
{
#include "aiger-1.9.4/aiger.h"
}

namespace sally {
namespace parser {

class aiger_parser : public internal_parser_interface {

  /** The term mangager */
  expr::term_manager& d_tm;

  /** File we're parsing */
  std::string d_filename;

  /** The command we're constructing */
  cmd::command* d_command;

  /** Type of aiger ids */
  typedef unsigned aiger_id_type;

  /** Aiger data */
  aiger* d_aiger;

  /** Map from aiger terms to terms */
  std::vector<expr::term_ref> d_aiger_to_term_map;

  /** Set the cache */
  inline
  void set_cache(aiger_id_type t_aiger, expr::term_ref t) {
    assert(t_aiger < d_aiger_to_term_map.size());
    d_aiger_to_term_map[t_aiger] = t;
  }

  /** Convert aiger to term while updating the cache */
  expr::term_ref aiger_to_term(aiger_id_type t_aiger);

public:

  aiger_parser(const system::context& ctx, const char* filename);
  virtual ~aiger_parser();

  cmd::command* parse_command();
  int get_current_parser_line() const;
  int get_current_parser_position() const;
  std::string get_filename() const;

};

expr::term_ref aiger_parser::aiger_to_term(aiger_id_type t_aiger) {

  assert(t_aiger < d_aiger_to_term_map.size());

  // Check in the cache
  if (!d_aiger_to_term_map[t_aiger].is_null()) {
    return d_aiger_to_term_map[t_aiger];
  }

  aiger_id_type t_aiger_unsigned = aiger_strip(t_aiger);
  aiger_id_type t_aiger_unsigned_not = aiger_not(t_aiger_unsigned);
  assert(d_aiger_to_term_map[t_aiger_unsigned].is_null());
  assert(d_aiger_to_term_map[t_aiger_unsigned_not].is_null());

  // Variables already in cache
  assert(aiger_is_input(d_aiger, t_aiger_unsigned) == 0);
  assert(aiger_is_latch(d_aiger, t_aiger_unsigned) == 0);

  // It's (t1 and t2), make it
  aiger_and* t_and = aiger_is_and(d_aiger, t_aiger_unsigned);
  assert(t_and->lhs == t_aiger_unsigned);

  // Make the term
  expr::term_ref t1 = aiger_to_term(t_and->rhs0);
  expr::term_ref t2 = aiger_to_term(t_and->rhs1);
  expr::term_ref t_unsigned = d_tm.mk_term(expr::TERM_AND, t1, t2);
  expr::term_ref t_unsigned_not = d_tm.mk_term(expr::TERM_NOT, t_unsigned);

  // Set the cache
  set_cache(t_aiger_unsigned, t_unsigned);
  set_cache(t_aiger_unsigned_not, t_unsigned_not);

  // Return the right value
  if (aiger_sign(t_aiger)) {
    return t_unsigned_not;
  } else {
    return t_unsigned;
  }
}

aiger_parser::aiger_parser(const system::context& ctx, const char* filename)
: d_tm(ctx.tm())
, d_filename(filename)
, d_command(0)
{
  // Init the parser
  aiger* a = aiger_init();
  const char* error = aiger_open_and_read_from_file(a, filename);
  if (error != 0) {
    throw parser_exception(error);
  }
  d_aiger = a;

  // Set the cache size
  d_aiger_to_term_map.resize(2*a->maxvar+2);

  // Check that we can handle it
  if (a->num_constraints > 0) {
    throw parser_exception("aiger unsupported: num_constraints > 0");
  }
  if (a->num_fairness > 0) {
    throw parser_exception("aiger unsupported: num_fairness > 0");
  }
  if (a->num_justice > 0) {
    throw parser_exception("aiger unsupported: num_justice > 0");
  }

  // Add true and false to the cache
  d_aiger_to_term_map[aiger_true] = d_tm.mk_boolean_constant(true);
  d_aiger_to_term_map[aiger_false] = d_tm.mk_boolean_constant(false);

  // The commands will be put here
  cmd::sequence* all_commands = new cmd::sequence();

  // Aiger format:
  // * inputs are sally input variables
  // * latches are sally state variables
  // * output are sally properties

  // Create the input and state variables
  std::vector<std::string> input_names, state_names;
  std::vector<aiger_id_type> input_aiger_ids, state_aiger_ids;
  std::vector<expr::term_ref> input_types, state_types;
  // Aiger doesn't really distinguish between state and input, properties can
  // include input variables, so we make everything state
  for (size_t i = 0; i < a->num_inputs; ++ i) {
    if (a->inputs[i].name != 0) {
      state_names.push_back(a->inputs[i].name);
    } else {
      std::stringstream ss;
      ss << "i" << a->inputs[i].lit;
      state_names.push_back(ss.str());
    }
    state_types.push_back(d_tm.boolean_type());
    state_aiger_ids.push_back(a->inputs[i].lit);
  }

  for (size_t i = 0; i < a->num_latches; ++ i) {
    if (a->latches[i].name != 0) {
      state_names.push_back(a->latches[i].name);
    } else {
      std::stringstream ss;
      ss << "l" << a->latches[i].lit;
      state_names.push_back(ss.str());
    }
    state_types.push_back(d_tm.boolean_type());
    state_aiger_ids.push_back(a->latches[i].lit);
  }

  // Make the state type
  expr::term_ref input_type_ref = d_tm.mk_struct_type(input_names, input_types);
  expr::term_ref state_type_ref = d_tm.mk_struct_type(state_names, state_types);
  system::state_type* state_type = new system::state_type("aig", d_tm, state_type_ref, input_type_ref);
  cmd::command* state_type_declare = new cmd::declare_state_type("aig", state_type);
  all_commands->push_back(state_type_declare);

  // Get the variables
  const std::vector<expr::term_ref>& input_vars = state_type->get_variables(system::state_type::STATE_INPUT);
  const std::vector<expr::term_ref>& state_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  assert(input_vars.size() == input_aiger_ids.size());
  assert(state_vars.size() == state_aiger_ids.size());

  // Add to cache
  for (size_t i = 0; i < input_aiger_ids.size(); ++ i) {
    aiger_id_type t_aiger = input_aiger_ids[i];
    expr::term_ref t = input_vars[i];
    set_cache(t_aiger, t);
    aiger_id_type t_aiger_not = aiger_not(t_aiger);
    expr::term_ref t_not = d_tm.mk_term(expr::TERM_NOT, t);
    set_cache(t_aiger_not, t_not);
  }
  for (size_t i = 0; i < state_aiger_ids.size(); ++ i) {
    aiger_id_type t_aiger = state_aiger_ids[i];
    expr::term_ref t = state_vars[i];
    set_cache(t_aiger, t);
    aiger_id_type t_aiger_not = aiger_not(t_aiger);
    expr::term_ref t_not = d_tm.mk_term(expr::TERM_NOT, t);
    set_cache(t_aiger_not, t_not);
  }

  // We have all variables and constants in the cache now. We can construct
  // formulas.

  // Get the initial states and transition formula
  std::vector<expr::term_ref> initial_state_formulas;
  std::vector<expr::term_ref> transition_formulas;
  for (size_t i = 0; i < a->num_latches; ++ i) {
    // The latch (var)
    expr::term_ref var = aiger_to_term(a->latches[i].lit);
    expr::term_ref next_var = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, var);
    // From aiger doc:  Latches are always assumed to be initialized to zero.
    // but, reset is available, so i'll take that one
    expr::term_ref init_value = aiger_to_term(a->latches[i].reset);
    expr::term_ref init_eq = d_tm.mk_term(expr::TERM_EQ, var, init_value);
    initial_state_formulas.push_back(init_eq);
    // Transition
    assert(aiger_sign(a->latches[i].lit) == 0);
    expr::term_ref next_value = aiger_to_term(a->latches[i].next);
    expr::term_ref next_eq = d_tm.mk_term(expr::TERM_EQ, next_var, next_value);
    transition_formulas.push_back(next_eq);
  }

  // Define initial states
  expr::term_ref initial_state = d_tm.mk_and(initial_state_formulas);
  system::state_formula* initial_state_formula = new system::state_formula(d_tm, state_type, initial_state);

  // Define transition
  expr::term_ref transition = d_tm.mk_and(transition_formulas);
  system::transition_formula* transition_formula = new system::transition_formula(d_tm, state_type, transition);

  // Define system
  system::transition_system* aiger_system = new system::transition_system(state_type, initial_state_formula, transition_formula);
  cmd::command* define_system = new cmd::define_transition_system("system", aiger_system);
  all_commands->push_back(define_system);
  
  // Get the properties
  std::vector<system::state_formula*> queries;
  for (size_t i = 0; i < a->num_outputs; ++ i) {
    expr::term_ref bad_i = aiger_to_term(a->outputs[i].lit);
    expr::term_ref p_i = d_tm.mk_term(expr::TERM_NOT, bad_i);
    system::state_formula *p = new system::state_formula(d_tm, state_type, p_i);
    queries.push_back(p);
  }
  cmd::command* query = new cmd::query(ctx, "system", queries);
  all_commands->push_back(query);

  // Construct the final command
  d_command = all_commands;

  // Delete aiger
  aiger_reset(a);
}

aiger_parser::~aiger_parser()
{}

cmd::command* aiger_parser::parse_command() {
  // Just return the saved command, and mark it back to 0
  cmd::command* result = d_command;
  d_command = 0;
  return result;
}

int aiger_parser::get_current_parser_line() const {
  return 0;
}

int aiger_parser::get_current_parser_position() const {
  return 0;
}

std::string aiger_parser::get_filename() const {
  return d_filename;
}


internal_parser_interface* new_aiger_parser(const system::context& ctx, const char* filename) {
  return new aiger_parser(ctx, filename);
}

}
}
