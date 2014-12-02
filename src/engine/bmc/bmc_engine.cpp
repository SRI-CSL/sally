/*
 * bmc_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/bmc/bmc_engine.h"

#include "smt/factory.h"

#include <sstream>
#include <iostream>

namespace sal2 {
namespace bmc {

bmc_engine::bmc_engine(const system::context& ctx)
: engine(ctx)
, d_trace(0)
{
  // Make the solver
  d_solver = smt::factory::mk_default_solver(ctx.tm(), ctx.get_options());
}

bmc_engine::~bmc_engine() {
  delete d_solver;
  delete d_trace;
}

bmc_engine::result bmc_engine::query(const system::transition_system& ts, const system::state_formula* sf) {

  // Scope for push/pop on the solver
  smt::solver_scope scope(d_solver);
  scope.push();

  // The trace we are building
  if (d_trace) { delete d_trace; }
  d_trace = new system::state_trace(ts.get_state_type());

  // Initial states
  expr::term_ref initial_states = ts.get_initial_states();
  d_solver->add(d_trace->get_state_formula(initial_states, 0));

  // Transition formula
  expr::term_ref transition_formula = ts.get_transition_relation();

  // The property
  expr::term_ref property = sf->get_formula();

  // BMC loop
  unsigned k = 0;
  while (true) {

    if (output::get_verbosity(std::cout) > 0) {
      std::cout << "BMC: checking " << k << std::endl;
    }

    // Check the current unrolling
    scope.push();
    expr::term_ref property_not = tm().mk_term(expr::TERM_NOT, property);
    d_solver->add(d_trace->get_state_formula(property_not, k));
    smt::solver::result r = d_solver->check();

    if (output::get_verbosity(std::cout) > 0) {
      std::cout << "BMC: got " << r << std::endl;
    }

    // See what happened
    switch(r) {
    case smt::solver::SAT: {
      expr::model m(tm());
      d_solver->get_model(m);
      d_trace->add_model(m);
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

    // Did we go overboard
    if (ctx().get_options().has_option("bmc_max") > 0) {
      unsigned max = ctx().get_options().get_unsigned("bmc_max");
      if (k >= max) {
        return UNKNOWN;
      }
    }

    // Unroll once more
    d_solver->add(d_trace->get_transition_formula(transition_formula, k, k + 1));
    k = k + 1;
  }

  return UNKNOWN;
}

const system::state_trace* bmc_engine::get_trace() {
  return d_trace;
}

}
}
