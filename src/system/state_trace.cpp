/*
 * state_trace.cpp
 *
 *  Created on: Nov 28, 2014
 *      Author: dejan
 */

#include "system/state_trace.h"

#include <sstream>

namespace sal2 {
namespace system {

state_trace::state_trace(const state_type* st)
: d_state_type(st)
{}

expr::term_manager& state_trace::tm() const {
  return d_state_type->tm();
}

expr::term_ref state_trace::get_state_variables(size_t k) {
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

expr::term_ref state_trace::get_state_formula(expr::term_ref sf, size_t k) {
  // Setup the substitution map
  expr::term_manager::substitution_map subst;
  std::vector<expr::term_ref> from_vars;
  std::vector<expr::term_ref> to_vars;
  tm().get_variables(d_state_type->get_state(state_type::STATE_CURRENT), from_vars);
  tm().get_variables(get_state_variables(k), to_vars);
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
  tm().get_variables(d_state_type->get_state(state_type::STATE_CURRENT), from_vars);
  tm().get_variables(d_state_type->get_state(state_type::STATE_NEXT), from_vars);
  tm().get_variables(get_state_variables(i), to_vars);
  tm().get_variables(get_state_variables(j), to_vars);
  for (size_t i = 0; i < from_vars.size(); ++ i) {
    subst[from_vars[i]] = to_vars[i];
  }
  // Substitute
  return tm().substitute(tf, subst);
}

}
}
