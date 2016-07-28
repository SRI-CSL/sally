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

#include "trace_helper.h"

#include "expr/gc_relocator.h"

#include <sstream>

namespace sally {
namespace system {

trace_helper::trace_helper(const state_type* st)
: gc_participant(st->tm())
, d_state_type(st)
, d_model_size(0)
{}

size_t trace_helper::size() const {
  return d_state_variables_structs.size();
}

expr::term_manager& trace_helper::tm() const {
  return d_state_type->tm();
}

void trace_helper::ensure_variables(size_t k) {
  assert(d_state_variables_structs.size() == d_input_variables_structs.size());
  // Ensure we have enough
  while (d_state_variables_structs.size() <= k) {
    // State variable
    std::stringstream ss_state;
    ss_state << "s" << d_state_variables_structs.size();
    expr::term_ref state_var_struct = tm().mk_variable(ss_state.str(), d_state_type->get_state_type_var());
    d_state_variables_structs.push_back(expr::term_ref_strong(tm(), state_var_struct));
    d_state_variables.push_back(std::vector<expr::term_ref>());
    get_struct_variables(state_var_struct, d_state_variables.back());
    // Input variable
    std::stringstream ss_input;
    ss_input << "i" << d_input_variables_structs.size();
    expr::term_ref input_var_struct = tm().mk_variable(ss_input.str(), d_state_type->get_input_type_var());
    d_input_variables_structs.push_back(expr::term_ref_strong(tm(), input_var_struct));
    d_input_variables.push_back(std::vector<expr::term_ref>());
    get_struct_variables(input_var_struct, d_input_variables.back());

    // Add a new substitution map
    d_subst_maps_state_to_trace.push_back(expr::term_manager::substitution_map());
    d_subst_maps_trace_to_state.push_back(expr::term_manager::substitution_map());
    expr::term_manager::substitution_map& subst_state_to_trace = d_subst_maps_state_to_trace.back();
    expr::term_manager::substitution_map& subst_trace_to_state = d_subst_maps_trace_to_state.back();
    // Variables of the state type
    const std::vector<expr::term_ref>& state_vars = d_state_type->get_variables(state_type::STATE_CURRENT);
    // Variable to rename them to (k-the step)
    const std::vector<expr::term_ref>& frame_vars = d_state_variables.back();
    for (size_t i = 0; i < state_vars.size(); ++ i) {
      subst_state_to_trace[state_vars[i]] = frame_vars[i];
      subst_trace_to_state[frame_vars[i]] = state_vars[i];
    }

  }
  assert(d_state_variables_structs.size() > k);
  assert(d_input_variables_structs.size() > k);
}

expr::term_ref trace_helper::get_state_struct_variable(size_t k) {
  // Return the variable
  ensure_variables(k);
  return d_state_variables_structs[k];
}

expr::term_ref trace_helper::get_input_struct_variable(size_t k) {
  // Return the variable
  ensure_variables(k);
  return d_input_variables_structs[k];
}

void trace_helper::get_struct_variables(expr::term_ref s, std::vector<expr::term_ref>& out) const {
  const expr::term& s_term = tm().term_of(s);
  size_t size = tm().get_struct_size(s_term);
  for (size_t i = 0; i < size; ++ i) {
    out.push_back(tm().get_struct_field(s_term, i));
  }
}

const std::vector<expr::term_ref>& trace_helper::get_state_variables(size_t k) {
  ensure_variables(k);
  return d_state_variables[k];
}

const std::vector<expr::term_ref>& trace_helper::get_input_variables(size_t k) {
  ensure_variables(k);
  return d_input_variables[k];
}

expr::term_ref trace_helper::get_state_formula(expr::term_ref sf, size_t k) {
  ensure_variables(k);
  return tm().substitute_and_cache(sf, d_subst_maps_state_to_trace[k]);
}

expr::term_ref trace_helper::get_state_formula(size_t k, expr::term_ref sf) {
  ensure_variables(k);
  return tm().substitute_and_cache(sf, d_subst_maps_trace_to_state[k]);
}

expr::term_ref trace_helper::get_transition_formula(expr::term_ref tf, size_t k) {
  // Setup the substitution map
  expr::term_manager::substitution_map subst;
  // Variables in the state type
  std::vector<expr::term_ref> from_vars;
  const std::vector<expr::term_ref>& current_vars = d_state_type->get_variables(state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& input_vars = d_state_type->get_variables(state_type::STATE_INPUT);
  const std::vector<expr::term_ref>& next_vars = d_state_type->get_variables(state_type::STATE_NEXT);
  from_vars.insert(from_vars.end(), current_vars.begin(), current_vars.end());
  from_vars.insert(from_vars.end(), input_vars.begin(), input_vars.end());
  from_vars.insert(from_vars.end(), next_vars.begin(), next_vars.end());

  // Variables in from k -> k + 1
  std::vector<expr::term_ref> to_vars;
  get_struct_variables(get_state_struct_variable(k), to_vars);
  get_struct_variables(get_input_struct_variable(k), to_vars);
  get_struct_variables(get_state_struct_variable(k+1), to_vars);

  assert(from_vars.size() == to_vars.size());

  for (size_t i = 0; i < from_vars.size(); ++ i) {
    subst[from_vars[i]] = to_vars[i];
  }
  // Substitute
  return tm().substitute_and_cache(tf, subst);
}

expr::model::ref trace_helper::get_model() const {
  return d_model;
}

void trace_helper::set_model(expr::model::ref m, size_t m_size) {
  d_model = m;
  assert(d_model_size <= d_state_variables_structs.size());
  d_model_size = m_size;
}

void trace_helper::to_stream(std::ostream& out) const {

  d_state_type->use_namespace();
  d_state_type->use_namespace(state_type::STATE_CURRENT);
  d_state_type->use_namespace(state_type::STATE_INPUT);

  out << "(trace " << std::endl;

  // Variables to use for printing names
  const std::vector<expr::term_ref> state_vars = d_state_type->get_variables(state_type::STATE_CURRENT);
  const std::vector<expr::term_ref> input_vars = d_state_type->get_variables(state_type::STATE_INPUT);

  // Output the values
  for (size_t k = 0; k < d_model_size; ++ k) {

    // The state variables
    out << "  (state" << std::endl;
    std::vector<expr::term_ref> state_vars_k;
    get_struct_variables(d_state_variables_structs[k], state_vars_k);
    assert(state_vars.size() == state_vars_k.size());
    for (size_t i = 0; i < state_vars_k.size(); ++ i) {
      out << "    (" << state_vars[i] << " " << d_model->get_variable_value(state_vars_k[i]) << ")" << std::endl;
    }
    out << "  )" << std::endl;

    // The input variables (except the last one)
    if (k + 1 < d_model_size) {
      out << "  (input" << std::endl;
      std::vector<expr::term_ref> input_vars_k;
      get_struct_variables(d_input_variables_structs[k], input_vars_k);
      assert(input_vars.size() == input_vars_k.size());
      for (size_t i = 0; i < input_vars_k.size(); ++ i) {
        out << "    (" << input_vars[i] << " " << d_model->get_variable_value(input_vars_k[i]) << ")" << std::endl;
      }
      out << "  )" << std::endl;
    }

  }

  out << ")" << std::endl;

  d_state_type->tm().pop_namespace();
  d_state_type->tm().pop_namespace();
  d_state_type->tm().pop_namespace();
}

bool trace_helper::is_true_in_frame(size_t frame, expr::term_ref f, expr::model::ref model) {
  // Return
  ensure_variables(frame);
  return model->is_true(f, d_subst_maps_state_to_trace[frame]);
}

bool trace_helper::is_false_in_frame(size_t frame, expr::term_ref f, expr::model::ref model) {
  // Return
  ensure_variables(frame);
  assert(frame < d_subst_maps_state_to_trace.size());
  return model->is_false(f, d_subst_maps_state_to_trace[frame]);
}

std::ostream& operator << (std::ostream& out, const trace_helper& trace) {
  trace.to_stream(out);
  return out;
}

void trace_helper::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_state_variables_structs);
}

}
}
