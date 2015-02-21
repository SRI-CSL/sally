/*
 * kind_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/kind/kind_engine.h"

#include "smt/factory.h"
#include "system/state_trace.h"

#include "utils/trace.h"

#include <sstream>
#include <iostream>

namespace sally {
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

engine::result kind_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

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
  d_trace = new system::state_trace(ts->get_state_type());

  // Initial states go to solver 1
  expr::term_ref initial_states = ts->get_initial_states();
  d_solver_1->add(d_trace->get_state_formula(initial_states, 0), smt::solver::CLASS_A);

  // Transition formula
  expr::term_ref transition_formula = ts->get_transition_relation();

  // The property
  expr::term_ref property = sf->get_formula();

  // The terms we use in the unrolling
  expr::term_ref property_k = d_trace->get_state_formula(property, 0);
  expr::term_ref property_not_k = tm().mk_term(expr::TERM_NOT, property_k);
  expr::term_ref transition_k;

  // The options
  unsigned kind_min = ctx().get_options().get_unsigned("kind-min");
  unsigned kind_max = ctx().get_options().get_unsigned("kind-max");

  // Induction loop
  unsigned k = 0;
  while (true) {

    MSG(1) << "K-Induction: checking initialization " << k << std::endl;

    // Check the current unrolling (1)
    scope1.push();
    d_solver_1->add(property_not_k, smt::solver::CLASS_A);
    smt::solver::result r_1 = d_solver_1->check();

    MSG(1) << "K-Induction: got " << r_1 << std::endl;

    // See what happened
    switch(r_1) {
    case smt::solver::SAT: {
      expr::model m(tm(), false);
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

    // For (2) add property and transition
    d_solver_2->add(property_k, smt::solver::CLASS_A);

    // Unroll the transition relation once more
    transition_k = d_trace->get_transition_formula(transition_formula, k, k+1);

    // For (2) add property and transition
    d_solver_2->add(transition_k, smt::solver::CLASS_A);

    // Should we do the check at k
    bool check_consecution = k >= kind_min;
    if (check_consecution) {
      MSG(1) << "K-Induction: checking consecution " << k << std::endl;
    }

    // Unroll the propety once more
    k = k + 1;
    property_k = d_trace->get_state_formula(property, k);
    property_not_k = tm().mk_term(expr::TERM_NOT, property_k);

    // Check the current unrolling (2)
    if (check_consecution) {
      scope2.push();
      d_solver_2->add(property_not_k, smt::solver::CLASS_A);
      smt::solver::result r_2 = d_solver_2->check();

      MSG(1) << "K-Induction: got " << r_2 << std::endl;

      // See what happened
      switch (r_2) {
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

    // Did we go overboard
    if (k > kind_max) {
      return UNKNOWN;
    }

    // One more transition for solver 1
    d_solver_1->add(transition_k, smt::solver::CLASS_A);
  }

  return UNKNOWN;
}

const system::state_trace* kind_engine::get_trace() {
  return d_trace;
}


}
}
