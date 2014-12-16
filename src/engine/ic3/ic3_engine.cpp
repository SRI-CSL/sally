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

expr::term_ref ic3_engine::check_sat(size_t k, expr::term_ref F) {

  smt::solver* solver = get_solver(k);
  smt::solver_scope scope(get_solver(k));

  if (!F.is_null()) {
    scope.push();
    solver->add(F);
  }

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
  expr::term_ref F_next = d_state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
  expr::term_ref F_next_not = tm().mk_term(expr::TERM_NOT, F_next);
  return check_sat(k, F_next_not);
}

void ic3_engine::add(size_t k, expr::term_ref F) {
  // Add to the frame
  // Add to solver
  get_solver(k)->add(F);
  // Add to induction obligations
  d_induction_obligations.push(obligation(k, F));
}

bool ic3_engine::frames_equal(size_t i, size_t j) const {
  return true;
}


engine::result ic3_engine::query(const system::transition_system& ts, const system::state_formula* sf) {

  expr::term_ref G;

  // The initial state
  expr::term_ref I = ts.get_initial_states();
  add(0, I);

  // The property we're trying to prove
  expr::term_ref P = sf->get_formula();

  // Check that P holds in the initial state
  expr::term_ref P_not = tm().mk_term(expr::TERM_BV_NOT, P);
  G = check_sat(0, P_not);
  if (!G.is_null()) {
    // Invalid, property is not valid
    return engine::INVALID;
  } else {
    // Add P to the initial state
    add(0, P);
  }

  for (;;) {

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    obligation io = d_induction_obligations.top();
    size_t io_frame = io.get_frame();
    expr::term_ref io_formula = io.get_formula();

    // Check if inductive
    G = check_inductive(io_frame, io_formula);
    if (G.is_null()) {
      // Valid, remove from obligations and push forward
      d_induction_obligations.pop();
      add(io_frame + 1, io_formula);
      // Check if we're done
      if (frames_equal(io_frame, io_frame + 1)) {
          return engine::VALID;
      }
      // Continue with the next obligation
      continue;
    }

    // The obligation not valid, try to extend to full counter-example
    for (;;) {

      // Get the next satisfiability obligations
      obligation so = d_sat_obligations.top();
      size_t so_frame = so.get_frame();
      expr::term_ref so_formula = so.get_formula();

      // Check if the obligation is sat
      G = check_sat(so_frame, so_formula);
      if (G.is_null()) {

      }

      // If this is a full counterexample
      if (so_frame == 0) {
        // If this was the property we just disproved, we're invalid
        if (io_formula == P) {
          return engine::INVALID;
        }
      }
    }

  }

  return UNKNOWN;
}

const system::state_trace* ic3_engine::get_trace() {
  return 0;
}


}
}
