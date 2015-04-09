/*
 * state_trace.cpp
 *
 *  Created on: Nov 28, 2014
 *      Author: dejan
 */

#include "system/state_trace.h"
#include "expr/gc_relocator.h"

#include <sstream>

namespace sally {
namespace system {

state_trace::state_trace(const state_type* st)
: gc_participant(st->tm())
, d_state_type(st)
, d_model(st->tm(), true)
{}

expr::term_manager& state_trace::tm() const {
  return d_state_type->tm();
}

expr::term_ref state_trace::get_state_type_variable(size_t k) {
  // Ensure we have enough
  while (d_state_variables.size() <= k) {
    std::stringstream ss;
    ss << "s" << d_state_variables.size();
    expr::term_ref var = tm().mk_variable(ss.str(), d_state_type->get_type());
    d_state_variables.push_back(expr::term_ref_strong(tm(), var));
  }
  // Return the variable
  return d_state_variables[k];
}

void state_trace::get_state_variables(expr::term_ref state_type_var, std::vector<expr::term_ref>& vars) const {
  const expr::term& state_type_var_term = tm().term_of(state_type_var);
  size_t size = tm().get_struct_size(state_type_var_term);
  for (size_t i = 0; i < size; ++ i) {
    vars.push_back(tm().get_struct_field(state_type_var_term, i));
  }
}

void state_trace::get_state_variables(size_t k, std::vector<expr::term_ref>& vars) {
  get_state_variables(get_state_type_variable(k), vars);
}

expr::term_ref state_trace::get_state_formula(expr::term_ref sf, size_t k) {
  // Setup the substitution map
  expr::term_manager::substitution_map subst;
  std::vector<expr::term_ref> from_vars;
  std::vector<expr::term_ref> to_vars;
  get_state_variables(d_state_type->get_state_type_variable(state_type::STATE_CURRENT), from_vars);
  get_state_variables(get_state_type_variable(k), to_vars);
  for (size_t i = 0; i < from_vars.size(); ++ i) {
    subst[from_vars[i]] = to_vars[i];
  }
  // Substitute
  return tm().substitute(sf, subst);
}

expr::term_ref state_trace::get_transition_formula(expr::term_ref tf, size_t i, size_t j) {
  assert(i < j);
  // Setup the substitution map
  expr::term_manager::substitution_map subst;
  std::vector<expr::term_ref> from_vars;
  std::vector<expr::term_ref> to_vars;
  get_state_variables(d_state_type->get_state_type_variable(state_type::STATE_CURRENT), from_vars);
  get_state_variables(d_state_type->get_state_type_variable(state_type::STATE_NEXT), from_vars);
  get_state_variables(get_state_type_variable(i), to_vars);
  get_state_variables(get_state_type_variable(j), to_vars);
  for (size_t i = 0; i < from_vars.size(); ++ i) {
    subst[from_vars[i]] = to_vars[i];
  }
  // Substitute
  return tm().substitute(tf, subst);
}

void state_trace::add_model(const expr::model& m) {
  expr::model::const_iterator it = m.values_begin();
  for (; it != m.values_end(); ++ it) {
    d_model.set_variable_value(it->first, it->second);
  }
}

void state_trace::add_model(const expr::model& m, state_type::var_class vc, size_t k) {

  // Setup the substitution map
  expr::term_manager::substitution_map subst;
  std::vector<expr::term_ref> from_vars;
  std::vector<expr::term_ref> to_vars;
  get_state_variables(d_state_type->get_state_type_variable(vc), from_vars);
  get_state_variables(get_state_type_variable(k), to_vars);
  for (size_t i = 0; i < from_vars.size(); ++ i) {
    subst[from_vars[i]] = to_vars[i];
  }

  expr::model::const_iterator it = m.values_begin();
  for (; it != m.values_end(); ++ it) {
    if (subst.find(it->first) != subst.end()) {
      d_model.set_variable_value(subst[it->first], it->second);
    }
  }
}

void state_trace::to_stream(std::ostream& out) const {

  d_state_type->use_namespace();
  d_state_type->use_namespace(state_type::STATE_CURRENT);

  out << "(trace " << std::endl;

  // Output the variables
  std::vector<expr::term_ref> state_vars;
  get_state_variables(d_state_type->get_state_type_variable(state_type::STATE_CURRENT), state_vars);

  // Output the values
  for (size_t k = 0; k < d_state_variables.size(); ++ k) {
    out << "  (frame" << std::endl;

    std::vector<expr::term_ref> state_vars_k;
    get_state_variables(d_state_variables[k], state_vars_k);
    for (size_t i = 0; i < state_vars.size(); ++ i) {
      expr::term_ref var = state_vars_k[i];
      out << "    (" << state_vars[i] << " ";
      out <<  d_model.get_variable_value(var);
      out << ")" << std::endl;
    }
    out << "  )" << std::endl;
  }

  out << ")" << std::endl;

  d_state_type->tm().pop_namespace();
  d_state_type->tm().pop_namespace();
}

void state_trace::resize_to(size_t size) {
  if (size < d_state_variables.size()) {
    d_state_variables.resize(size);
  }
}

std::ostream& operator << (std::ostream& out, const state_trace& trace) {
  trace.to_stream(out);
  return out;
}

void state_trace::gc_collect(const expr::gc_info& gc_reloc) {
  size_t ret;
  ret = gc_reloc.collect(d_state_variables.begin(), d_state_variables.end());
  assert(ret == 0);
}

}
}
