/*
 * ic3_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/ic3/ic3_engine.h"

#include "smt/factory.h"
#include "system/state_trace.h"

#include <cassert>
#include <sstream>
#include <iostream>

namespace sal2 {
namespace ic3 {

ic3_engine::ic3_engine(const system::context& ctx)
: engine(ctx)
, d_state_type(0)
{
}

smt::solver* ic3_engine::get_solver(size_t k) {
  while (k >= d_solvers.size()) {
    d_solvers.push_back(smt::factory::mk_default_solver(tm(), ctx().get_options()));
  }
  return d_solvers[k];
}

ic3_engine::~ic3_engine() {
  for (size_t k = 0; k < d_solvers.size(); ++ k) {
    delete d_solvers[k];
  }
}

expr::term_ref ic3_engine::check_one_step_reachable(size_t k, expr::term_ref F) {

  assert(k > 0);

  // Get the solver
  smt::solver* solver = get_solver(k-1);
  smt::solver_scope scope(solver);

  // Add the formula (moving
  scope.push();
  expr::term_ref F_next = d_state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
  solver->add(F_next);

  // Figure out the result
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    const std::vector<expr::term_ref>& state_vars = d_state_type->get_variables(system::state_type::STATE_CURRENT);
    return solver->generalize(state_vars);
  }
  case smt::solver::UNSAT:
    // Unsat, we return NULL
    return expr::term_ref();
  default:
    throw exception("SMT unknown result.");
  }

  return expr::term_ref();
}

expr::term_ref ic3_engine::check_inductive(size_t k, expr::term_ref F) {
  assert(!F.is_null());
  expr::term_ref F_not = tm().mk_term(expr::TERM_NOT, F);
  return check_one_step_reachable(k+1, F_not);
}

void ic3_engine::add(size_t k, expr::term_ref F) {
  // Add to the frame

  // Add to solvers
  get_solver(k)->add(F);
  if (k > 0) {
    expr::term_ref F_next = d_state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
    get_solver(k-1)->add(F_next);
  }

  // Add to induction obligations
  d_induction_obligations.push(obligation(k, F));
}

bool ic3_engine::frames_equal(size_t i, size_t j) const {
  return true;
}


engine::result ic3_engine::query(const system::transition_system& ts, const system::state_formula* sf) {

  expr::term_ref G;

  // Remember the state type
  d_state_type = sf->get_state_type();

  // The initial state
  expr::term_ref I = ts.get_initial_states();
  add(0, I);

  // The property we're trying to prove
  expr::term_ref P = sf->get_formula();

  // Check that P holds in the initial state
  expr::term_ref P_not = tm().mk_term(expr::TERM_NOT, P);
  smt::solver* solver0 = get_solver(0);
  solver0->add(P_not);
  smt::solver::result r = solver0->check();
  solver0->pop();
  switch (r) {
  case smt::solver::SAT:
    // Invalid, property is not valid
    return engine::INVALID;
  case smt::solver::UNSAT:
    // Valid, we continue with P
    add(0, P);
    break;
  default:
    throw exception("Unknown SMT result.");
  }

  for (;;) {

    assert(!d_induction_obligations.empty());
    assert(d_reachability_obligations.empty());

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    obligation ind = d_induction_obligations.top();

    // Check if inductive
    G = check_inductive(ind.frame(), ind.formula());
    if (G.is_null()) {
      // Proved, we can remove it
      d_induction_obligations.pop();
      // Valid, push forward
      add(ind.frame() + 1, ind.formula());
      // Check if we're done
      if (frames_equal(ind.frame(), ind.frame() + 1)) {
          return engine::VALID;
      }
      // Continue with the next obligation
      continue;
    }

    // The induction not valid, try to extend to full counter-example
    while (!d_reachability_obligations.empty()) {

      // Get the next satisfiability obligations
      obligation reach = d_reachability_obligations.top();

      // Check if the obligation is sat
      G = check_one_step_reachable(reach.frame(), reach.formula());
      if (G.is_null()) {
        // Proven, remove from obligations
        d_reachability_obligations.pop();
        // Add the negation of the obligation to known facts
        add(reach.frame(), tm().mk_term(expr::TERM_NOT, reach.formula()));
      } else {
        // If this is a full counterexample
        if (reach.frame() == 1) {
          // If this was the property we just disproved, we're invalid
          if (ind.formula() == P) {
            return engine::INVALID;
          }
          break;
        }
      }
    }

    // Clear reachability obligations, if any
    d_reachability_obligations.clear();
  }

  return UNKNOWN;
}

const system::state_trace* ic3_engine::get_trace() {
  return 0;
}


}
}
