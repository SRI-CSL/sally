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

#include "engine/bmc/bmc_engine.h"

#include "smt/factory.h"
#include "utils/trace.h"

#include <sstream>
#include <iostream>

namespace sally {
namespace bmc {

bmc_engine::bmc_engine(const system::context& ctx)
: engine(ctx)
, d_trace(0)
{
  // Make the solver
  d_solver = smt::factory::mk_default_solver(ctx.tm(), ctx.get_options(), ctx.get_statistics());
}

bmc_engine::~bmc_engine() {
  delete d_solver;
  delete d_trace;
}

engine::result bmc_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Scope for push/pop on the solver
  smt::solver_scope scope(d_solver);
  scope.push();

  // The trace we are building
  if (d_trace) { delete d_trace; }
  d_trace = new system::state_trace(ts->get_state_type());

  // Initial states
  expr::term_ref initial_states = ts->get_initial_states();
  d_solver->add(d_trace->get_state_formula(initial_states, 0), smt::solver::CLASS_A);

  // Transition formula
  expr::term_ref transition_formula = ts->get_transition_relation();

  // The property
  expr::term_ref property = sf->get_formula();

  // The loop
  size_t bmc_min = ctx().get_options().get_unsigned("bmc-min");
  size_t bmc_max = ctx().get_options().get_unsigned("bmc-max");

  // BMC loop
  for (size_t k = 0; k <= bmc_max; ++ k) {

    // Add the variables to the solver
    const std::vector<expr::term_ref>& state_vars = d_trace->get_state_variables(k);
    d_solver->add_variables(state_vars.begin(), state_vars.end(), smt::solver::CLASS_A);

    // Check the current unrolling
    if (k >= bmc_min) {

      MSG(1) << "BMC: checking " << k << std::endl;

      scope.push();
      expr::term_ref property_not = tm().mk_term(expr::TERM_NOT, property);
      d_solver->add(d_trace->get_state_formula(property_not, k), smt::solver::CLASS_A);
      smt::solver::result r = d_solver->check();

      MSG(1) << "BMC: got " << r << std::endl;

      // See what happened
      switch (r) {
      case smt::solver::SAT: {
        expr::model::ref m = d_solver->get_model();
        d_trace->set_model(m, k+1);
        return INVALID;
      }
      case smt::solver::UNKNOWN:
        return UNKNOWN;
      case smt::solver::UNSAT:
        // No counterexample found, continue
        break;
      default:
        assert(false);
      }

      // Pop the solver
      scope.pop();
    }

    // Unroll once more
    d_solver->add(d_trace->get_transition_formula(transition_formula, k), smt::solver::CLASS_A);
    const std::vector<expr::term_ref>& input_vars = d_trace->get_input_variables(k);
    d_solver->add_variables(input_vars.begin(), input_vars.end(), smt::solver::CLASS_A);
  }

  return UNKNOWN;
}

const system::state_trace* bmc_engine::get_trace() {
  return d_trace;
}

}
}
