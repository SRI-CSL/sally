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

expr::term_ref ic3_engine::check(size_t k, expr::term_ref F) {

  smt::solver* solver = get_solver(k);
  smt::solver_scope scope(get_solver(k));

  if (!F.is_null()) {
    scope.push();
    solver->add(F);
  }

  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT:
    return solver->generalize(d_next_variables);
  case smt::solver::UNSAT:
    // Unsat, we return NULL
    return expr::term_ref();
  default:
    throw exception("SMT unknown result.");
  }

  return expr::term_ref();
}

void ic3_engine::add(size_t k, expr::term_ref F) {
  get_solver(k)->add(F);
  add_induction_obligation(k, f);
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
  G = check(0, P_not);
  if (!G.is_null()) {
    return engine::INVALID;
  }

  // Add P to the initial state
  add(0, P);

  for (;;) {
    // Major loop: Pick a formula to try and prove inductive, i.e.
    // that F_k & P & T => P'
    induction_obligation io = pop_induction_obligation();
    G = check_inductive(io.k, io.P);
    if (G.is_null()) {
      // Valid, push it forward
      push_forward(o);
      // Check if proven
      if (frames_equal(o, o_next)) {
          return engine::VALID;
      }
      continue;
    }

    // The obligation not valid, try to extend to full counter-example
    for (;;) {


      // If this was the property we just disproved, we're invalid
      if (io.P == P) {
        return engine::INVALID;
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
