/*
 * kind_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/kind/kind_engine.h"

#include "smt/factory.h"
#include "system/state_trace.h"

#include <sstream>

namespace sal2 {
namespace kind {

kind_engine::kind_engine(const system::context& ctx)
: engine(ctx)
, d_trace(0)
{
  // Make the solvers
  d_solver_1 = smt::factory::mk_default_solver(ctx.tm(), ctx.get_options());
  d_solver_2 = smt::factory::mk_default_solver(ctx.tm(), ctx.get_options());
}

kind_engine::~kind_engine() {
  delete d_solver_1;
  delete d_solver_2;
  delete d_trace;
}

kind_engine::result kind_engine::query(const system::transition_system& ts, const system::state_formula* sf) {

  /*

    We try to find a k such that:
    (1) P holds at steps 0, ..., k-1, i.e.
        I and T_0 and ... and T_{i-1} => P(x_i), for 0 <= i < k
    (2) P holding at k consecutive step, implies it holds in the next one, i.e.
        and_{0 <= i < k} (P_i and T_i) => P_k

    Use two solvers:
    * solver 1 accumulates the antecedent of (1), i.e. I and T_0 and ... and T_{k-1}
    * solver 2 accumulates the antecedent of (2), i.e. P_0 and T_0 and ....P_{k-1} and T_{k-1}

    solver1: check (not P). if sat we found a counterexample.
    solver2: check (not P). if unsat we proved the property.

  */

  // Scopes for solver push/pop
  smt::solver_scope scope1(d_solver_1);
  smt::solver_scope scope2(d_solver_2);
  scope1.push();
  scope2.push();

  // The trace we are building
  if (d_trace) { delete d_trace; }
  d_trace = new system::state_trace(ts.get_state_type());

  // Initial states go to solver 1
  expr::term_ref initial_states = ts.get_initial_states();
  d_solver_1->add(d_trace->get_state_formula(initial_states, 0));

  // Transition formula
  expr::term_ref transition_fromula = ts.get_transition_relation();

  // The property
  expr::term_ref property = sf->get_formula();
  expr::term_ref property_not = tm().mk_term(expr::TERM_NOT, property);

  // Inductino loop
  unsigned k = 0;
  while (true) {

    if (output::get_verbosity(std::cout) > 0) {
      std::cout << "K-Inductino: checking intialization " << k << std::endl;
    }

    // Negataed property at k
    expr::term_ref property_not_k = d_trace->get_state_formula(property_not, k);

    // Check the current unrolling (1)
    scope1.push();
    d_solver_1->add(property_not_k);
    smt::solver::result r_1 = d_solver_1->check();

    if (output::get_verbosity(std::cout) > 0) {
      std::cout << "K-Induction: got " << r_1 << std::endl;
    }

    // See what happened
    switch(r_1) {
    case smt::solver::SAT: {
      expr::model m(tm());
      d_solver_1->get_model(m);
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
    scope1.pop();

    // Did we go overboard
    if (ctx().get_options().has_option("kind_max") > 0) {
      unsigned max = ctx().get_options().get_unsigned("kind_max");
      if (k >= max) {
        return UNKNOWN;
      }
    }

    // Check the current unrolling (2)
    if (k > 0) {
      scope2.push();
      d_solver_2->add(property_not_k);
      smt::solver::result r_2 = d_solver_2->check();

      if (output::get_verbosity(std::cout) > 0) {
        std::cout << "K-Induction: got " << r_2 << std::endl;
      }

      // See what happened
      switch(r_2) {
      case smt::solver::SAT:
        // Couldn't prove it, continue
        break;
      case smt::solver::UNKNOWN:
        return UNKNOWN;
      case smt::solver::UNSAT:
        // Proved it, done
        return VALID;
        break;
      default:
        assert(false);
      }

      // Pop the solver
      scope2.pop();
    }

    // Unroll once more
    expr::term_ref property_k = d_trace->get_state_formula(property, k);
    expr::term_ref transition_k = d_trace->get_transition_formula(transition_fromula, k, k+1);

    // For (1) just add the transition
    d_solver_1->add(transition_k);

    // For (2) add property and transition
    d_solver_2->add(property_k);
    d_solver_2->add(transition_k);

    // Continue
    k = k + 1;
  }

  return UNKNOWN;
}

const system::state_trace* kind_engine::get_trace() {
  return d_trace;
}


}
}
