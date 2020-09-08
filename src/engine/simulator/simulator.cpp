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

#include "simulator.h"

#include "smt/factory.h"
#include "utils/trace.h"

#include <sstream>
#include <iostream>

namespace sally {
namespace simulator {

simulator::simulator(const system::context& ctx)
: engine(ctx)
, d_trace(0)
{
}

simulator::~simulator() {}

engine::result simulator::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Make the solver
  smt::solver::ref d_solver(smt::factory::mk_default_solver(tm(), ctx().get_options(), ctx().get_statistics()));

  // The trace we are using
  d_trace = ts->get_trace_helper();
  d_trace->clear_model();

  // Initial states
  expr::term_ref initial_states = ts->get_initial_states();
  const std::vector<expr::term_ref>& state_vars = d_trace->get_state_variables(0);
  d_solver->add_variables(state_vars.begin(), state_vars.end(), smt::solver::CLASS_A);
  d_solver->add(d_trace->get_state_formula(initial_states, 0), smt::solver::CLASS_A);

  // Transition formula
  expr::term_ref transition_formula = ts->get_transition_relation();

  // The property
  expr::term_ref property = sf->get_formula();

  // The loop
  size_t simulator_min = ctx().get_options().get_unsigned("sim-min");
  size_t simulator_max = ctx().get_options().get_unsigned("sim-max");

  // Did we get an unknown result
  bool unknown = false;

  // Target we are looking for
  expr::term_ref target = tm().mk_boolean_constant(false);

  // BMC loop
  for (size_t k = 0; k <= simulator_max; ++ k) {
  
    target = tm().mk_or(target, d_trace->get_state_formula(property, k));

    // Check the current unrolling
    if (k >= simulator_min) {

      MSG(1) << "Simulator: checking " << k << std::endl;

      if (!d_solver->is_consistent()) {
        // Inconsistent unrolling, property trivially valid
        if (unknown) {
          return SILENT;
        } else {
          return SILENT;
        }
      }

      d_solver->push();
      d_solver->add(target, smt::solver::CLASS_A);
      smt::solver::result r = d_solver->check();

      MSG(1) << "Simulator: got " << r << std::endl;

      // See what happened
      switch (r) {
      case smt::solver::SAT: {
        expr::model::ref m = d_solver->get_model();
        d_trace->set_model(m, 0, k);
        return SILENT_WITH_TRACE;
      }
      case smt::solver::UNKNOWN:
        unknown = true;
      case smt::solver::UNSAT:
        // No counterexample found, continue
        break;
      default:
        assert(false);
      }

      // Pop the solver
      d_solver->pop();
    }

    // Add the variables to the solver
    const std::vector<expr::term_ref>& state_vars = d_trace->get_state_variables(k+1);
    d_solver->add_variables(state_vars.begin(), state_vars.end(), smt::solver::CLASS_A);
    const std::vector<expr::term_ref>& input_vars = d_trace->get_input_variables(k);
    d_solver->add_variables(input_vars.begin(), input_vars.end(), smt::solver::CLASS_A);
    // Unroll once more
    d_solver->add(d_trace->get_transition_formula(transition_formula, k), smt::solver::CLASS_A);
  }

  return SILENT;
}

const system::trace_helper* simulator::get_trace() {
  return d_trace;
}

engine::invariant simulator::get_invariant() {
  throw exception("Not supported.");
}

}
}
