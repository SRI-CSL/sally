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

#include "engine/kind/kind_engine.h"

#include "smt/factory.h"
#include "utils/trace.h"

#include <sstream>
#include <iostream>
#include "../../system/trace_helper.h"
#include <cassert>

namespace sally {
namespace kind {

kind_engine::kind_engine(const system::context& ctx)
: engine(ctx)
, d_trace(0)
, d_invariant(expr::term_ref(), 0)
{
}

kind_engine::~kind_engine() {
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

  /** SMT solver for proving (1) */
  smt::solver::ref solver1(smt::factory::mk_default_solver(tm(), ctx().get_options(), ctx().get_statistics()));
  /** SMT solver for proving (2) */
  smt::solver::ref solver2(smt::factory::mk_default_solver(tm(), ctx().get_options(), ctx().get_statistics()));

  // The trace we are building
  d_trace = ts->get_trace_helper();
  d_trace->clear_model();

  typedef std::vector<expr::term_ref> var_vec;

  // Add initial state variables
  const var_vec& x0 = d_trace->get_state_variables(0);
  solver1->add_variables(x0, smt::solver::CLASS_A);
  solver2->add_variables(x0, smt::solver::CLASS_A);

  // Initial states go to solver 1
  expr::term_ref initial_states = ts->get_initial_states();
  solver1->add(d_trace->get_state_formula(initial_states, 0), smt::solver::CLASS_A);

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

    // Did we go overboard
    if (k >= kind_max) {
      return UNKNOWN;
    }

    MSG(1) << "K-Induction: checking initialization " << k << std::endl;

    // Check the current unrolling (1)
    solver1->push();
    solver1->add(property_not_k, smt::solver::CLASS_A);
    smt::solver::result r_1 = solver1->check();

    MSG(1) << "K-Induction: got " << r_1 << std::endl;

    // See what happened
    switch(r_1) {
    case smt::solver::SAT: {
      // Get the model
      expr::model::ref m = solver1->get_model();
      // Add model to trace
      d_trace->set_model(m,0, k);
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
    solver1->pop();

    // Variables of the transition
    solver2->add_variables(d_trace->get_input_variables(k), smt::solver::CLASS_A);
    solver2->add_variables(d_trace->get_state_variables(k+1), smt::solver::CLASS_A);
    solver1->add_variables(d_trace->get_input_variables(k), smt::solver::CLASS_A);
    solver1->add_variables(d_trace->get_state_variables(k+1), smt::solver::CLASS_A);

    // For (2) add property and transition
    solver2->add(property_k, smt::solver::CLASS_A);

    // Unroll the transition relation once more
    transition_k = d_trace->get_transition_formula(transition_formula, k);

    // For (2) add property and transition
    solver2->add(transition_k, smt::solver::CLASS_A);

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
      solver2->push();
      solver2->add(property_not_k, smt::solver::CLASS_A);
      smt::solver::result r_2 = solver2->check_relaxed();

      MSG(1) << "K-Induction: got " << r_2 << std::endl;

      // See what happened
      switch (r_2) {
      case smt::solver::SAT:
      case smt::solver::UNKNOWN:
        // Couldn't prove it, continue
        break;
      case smt::solver::UNSAT:
        // Proved it, done
        d_invariant = invariant(property, k);
        return VALID;
        break;
      default:
        assert(false);
      }

      // Pop the solver
      solver2->pop();
    }

    // One more transition for solver 1
    solver1->add(transition_k, smt::solver::CLASS_A);
  }

  return UNKNOWN;
}

const system::trace_helper* kind_engine::get_trace() {
  return d_trace;
}

engine::invariant kind_engine::get_invariant() {
  return d_invariant;
}

}
}
