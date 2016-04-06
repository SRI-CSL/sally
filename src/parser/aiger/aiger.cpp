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
  command* d_command;

  /** Type of aiger ids */
  typedef unsigned aiger_id_type;

  /** Aiger data */
  aiger* d_aiger;

  /** Map from terms to aiger ids */
  typedef boost::unordered_map<expr::term_ref, aiger_id_type, expr::term_ref_hasher> term_to_aiger_map;
  /** Map from aiger ids to terms */
  typedef boost::unordered_map<aiger_id_type, expr::term_ref> aiger_to_term_map;

  /** Map from aiger terms to terms */
  aiger_to_term_map d_aiger_to_term_map;

  /** Map from term to aiger ids */
  term_to_aiger_map d_term_to_aiger_map;

  /** Set the cache t_aiger -> t (for both negated and not negated) */
  void set_cache(aiger_id_type t_aiger, expr::term_ref t);

  /** Convert aiger to term while updating the cache */
  expr::term_ref aiger_to_term(aiger_id_type t_aiger);

public:

  aiger_parser(const system::context& ctx, const char* filename);
  virtual ~aiger_parser();

  command* parse_command();
  int get_current_parser_line() const;
  int get_current_parser_position() const;
  std::string get_filename() const;

};

// Negate the term (don't do double negation)
expr::term_ref negate(expr::term_manager& tm, expr::term_ref t) {
  const expr::term& term = tm.term_of(t);
  if (term.op() == expr::TERM_NOT) {
    return term[0];
  } else {
    return tm.mk_term(expr::TERM_NOT, t);
  }
}

void aiger_parser::set_cache(aiger_id_type t_aiger, expr::term_ref t) {
  assert(d_aiger_to_term_map.find(t_aiger) == d_aiger_to_term_map.end());
  assert(d_term_to_aiger_map.find(t) == d_term_to_aiger_map.end());

  // Cache negated t also
  expr::term_ref t_not = negate(d_tm, t);

  // aiger -> term
  d_aiger_to_term_map[t_aiger] = t;
  d_aiger_to_term_map[aiger_not(t_aiger)] = t_not;

  // term -> aiger
  d_term_to_aiger_map[t] = t_aiger;
  d_term_to_aiger_map[t_not] = aiger_not(t_aiger);
}

expr::term_ref aiger_parser::aiger_to_term(aiger_id_type t_aiger) {

  // Check in the cache
  aiger_to_term_map::const_iterator find = d_aiger_to_term_map.find(t_aiger);
  if (find != d_aiger_to_term_map.end()) {
    return find->second;
  }

  aiger_id_type t_aiger_unsigned = aiger_strip(t_aiger);

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

  // Set the cache
  set_cache(t_aiger_unsigned, t_unsigned);

  // Return the right value
  if (aiger_sign(t_aiger)) {
    return d_tm.mk_term(expr::TERM_NOT, t_unsigned);
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

  // Add true and false to the cache
  expr::term_ref t_true = d_tm.mk_boolean_constant(true);
  expr::term_ref t_false = d_tm.mk_boolean_constant(false);
  d_aiger_to_term_map[aiger_true] = t_true;
  d_aiger_to_term_map[aiger_false] = t_false;
  d_term_to_aiger_map[t_true] = aiger_true;
  d_term_to_aiger_map[t_false] = aiger_false;

  // The commands will be put here
  sequence_command* all_commands = new sequence_command();

  // Aiger format:
  // * inputs are sally input variables
  // * latches are sally state variables
  // * output are sally properties

  // Create the input variables
  std::vector<std::string> input_names;
  std::vector<expr::term_ref> input_types;
  for (size_t i = 0; i < a->num_inputs; ++ i) {
    if (a->inputs[i].name != 0) {
      input_names.push_back(a->inputs[i].name);
    } else {
      std::stringstream ss;
      ss << "i" << i;
      input_names.push_back(ss.str());
    }
    input_types.push_back(d_tm.boolean_type());
  }

  // Create the state types
  std::vector<std::string> state_names;
  std::vector<expr::term_ref> state_types;
  for (size_t i = 0; i < a->num_latches; ++ i) {
    if (a->latches[i].name != 0) {
      state_names.push_back(a->latches[i].name);
    } else {
      std::stringstream ss;
      ss << "l" << i;
      state_names.push_back(ss.str());
    }
    state_types.push_back(d_tm.boolean_type());
  }

  // Make the state type
  expr::term_ref input_type_ref = d_tm.mk_struct_type(input_names, input_types);
  expr::term_ref state_type_ref = d_tm.mk_struct_type(state_names, state_types);
  system::state_type* state_type = new system::state_type("aiger_state_type", d_tm, state_type_ref, input_type_ref);
  command* state_type_declare = new declare_state_type_command("aiger_state_type", state_type);

  // Get the variables
  const std::vector<expr::term_ref>& input_vars = state_type->get_variables(system::state_type::STATE_INPUT);
  const std::vector<expr::term_ref>& state_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  assert(input_vars.size() == a->num_inputs);
  assert(state_vars.size() == a->num_latches);

  // Add to cache
  for (size_t i = 0; i < a->num_inputs; ++ i) {
    set_cache(a->inputs[i].lit, input_vars[i]);
  }
  for (size_t i = 0; i < a->num_latches; ++ i) {
    set_cache(a->latches[i].lit, state_vars[i]);
  }

  // We have all variables and constants in the cache now. We can construct
  // formulas.

  // Get the initial states and transition formula
  std::vector<expr::term_ref> initial_state_formulas;
  std::vector<expr::term_ref> transition_formulas;
  for (size_t i = 0; i < a->num_latches; ++ i) {
    // Reset = init
    initial_state_formulas.push_back(aiger_to_term(a->latches[i].reset));
    // Transition
    assert(aiger_sign(a->latches[i].lit) == 0);
    expr::term_ref var = aiger_to_term(a->latches[i].lit);
    expr::term_ref next_value = aiger_to_term(a->latches[i].next);
    expr::term_ref next_var = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, var);
    expr::term_ref eq = d_tm.mk_term(expr::TERM_EQ, next_var, next_value);
    transition_formulas.push_back(eq);
  }

  // Define initial states
  expr::term_ref initial_state = d_tm.mk_and(initial_state_formulas);
  system::state_formula* initial_state_formula = new system::state_formula(d_tm, state_type, initial_state);

  // Define transition
  expr::term_ref transition = d_tm.mk_and(transition_formulas);
  system::transition_formula* transition_formula = new system::transition_formula(d_tm, state_type, transition);

  // Define system
  system::transition_system* aiger_system = new system::transition_system(state_type, initial_state_formula, transition_formula);
  command* define_system = new define_transition_system_command("aiger_system", aiger_system);
  all_commands->push_back(define_system);
  
  // Get the properties
  for (size_t i = 0; i < a->num_outputs; ++ i) {
    expr::term_ref p_i = aiger_to_term(a->outputs[i].lit);
    system::state_formula *p = new system::state_formula(d_tm, state_type, p_i);
    command* query = new query_command(ctx, "aiger_system", p);
    all_commands->push_back(query);
  }

  // Construct the final command
  all_commands->push_back(state_type_declare);
  d_command = all_commands;

  // Delete aiger
  aiger_reset(a);
}

aiger_parser::~aiger_parser()
{}

command* aiger_parser::parse_command() {
  // Just return the saved command, and mark it back to 0
  command* result = d_command;
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
  return 0;
}

}
}
