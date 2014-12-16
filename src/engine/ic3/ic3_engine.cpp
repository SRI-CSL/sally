/*
 * ic3_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/ic3/ic3_engine.h"

#include "smt/factory.h"
#include "system/state_trace.h"
#include "utils/trace.h"

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

std::ostream& operator << (std::ostream& out, const ic3_engine& ic3) {
  ic3.to_stream(out);
  return out;
}

smt::solver* ic3_engine::get_solver(size_t k) {
  ensure_frame(k);
  return d_solvers[k];
}

ic3_engine::~ic3_engine() {
  for (size_t k = 0; k < d_solvers.size(); ++ k) {
    delete d_solvers[k];
  }
}

expr::term_ref ic3_engine::check_one_step_reachable(size_t k, expr::term_ref F) {
  assert(k > 0);

  // Get the solver of the previous frame
  smt::solver* solver = get_solver(k-1);
  smt::solver_scope scope(solver);

  // Add the formula (moving current -> next)
  scope.push();
  expr::term_ref F_next = d_state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
  solver->add(F_next);

  // Figure out the result
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    const std::vector<expr::term_ref>& state_vars = d_state_type->get_variables(system::state_type::STATE_NEXT);
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

expr::term_ref ic3_engine::check_inductive_at(size_t k, expr::term_ref F) {
  assert(!F.is_null());
  assert(d_frame_content[k].find(F) != d_frame_content[k].end());
  expr::term_ref F_not = tm().mk_term(expr::TERM_NOT, F);
  return check_one_step_reachable(k+1, F_not);
}

void ic3_engine::add_learnt(size_t k, expr::term_ref F) {
  // Ensure frame is setup
  ensure_frame(k);

  // Formula is either
  // * being pushed, so it's true up to k-1 and we're adding at k
  // * newly learnt, so it's not known from 0..k
  bool is_push = (k > 0 && d_frame_content[k-1].find(F) != d_frame_content[k-1].end());

  // Add to all frames from 0..k
  for(size_t i = is_push ? k : 0; i <= k; ++ i) {
    assert(d_frame_content[i].find(F) == d_frame_content[i].end());
    d_frame_content[i].insert(F);
    get_solver(i)->add(F);
    if (i > 0) {
      expr::term_ref F_next = d_state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
      get_solver(i-1)->add(F_next);
    }
  }

  // Add to induction obligations
  d_induction_obligations.push(obligation(k, F));
}

void ic3_engine::ensure_frame(size_t k) {
  while (d_solvers.size() <= k) {
    // Make the solver
    smt::solver* solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
    d_solvers.push_back(solver);
    // Add the transition relation
    solver->add(d_transition_system->get_transition_relation());
    // Add the frame content
    d_frame_content.push_back(formula_set());
  }
  assert(d_solvers.size() == d_frame_content.size());
}

engine::result ic3_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  expr::term_ref G;

  // Remember the input
  d_state_type = sf->get_state_type();
  d_transition_system = ts;

  // The initial state
  expr::term_ref I = ts->get_initial_states();
  add_learnt(0, I);

  // The property we're trying to prove
  expr::term_ref P = sf->get_formula();

  // Check that P holds in the initial state
  expr::term_ref P_not = tm().mk_term(expr::TERM_NOT, P);
  smt::solver* solver0 = get_solver(0);
  solver0->push();
  solver0->add(P_not);
  smt::solver::result r = solver0->check();
  solver0->pop();
  switch (r) {
  case smt::solver::SAT:
    // Invalid, property is not valid
    return engine::INVALID;
  case smt::solver::UNSAT:
    // Valid, we continue with P
    add_learnt(0, P);
    break;
  default:
    throw exception("Unknown SMT result.");
  }

  for (;;) {

    assert(!d_induction_obligations.empty());

    TRACE("ic3") << *this << std::endl;

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    obligation ind = d_induction_obligations.top();
    d_induction_obligations.pop();

    // Check if inductive
    TRACE("ic3") << "Checking inductive at " << ind.frame() << " for " << ind.formula() << std::endl;
    G = check_inductive_at(ind.frame(), ind.formula());

    // If inductive
    if (G.is_null()) {
      TRACE("ic3") << "is inductive" << std::endl;
      // Valid, push forward
      add_learnt(ind.frame() + 1, ind.formula());
      // Check if we're done
      if (d_frame_content[ind.frame()].size() == d_frame_content[ind.frame()+1].size()) {
        return engine::VALID;
      }
      // Go for the next obligation
      continue;
    }

    TRACE("ic3") << "not inductive" << std::endl;

    // If we're checking frame 0, there is nothing to do
    if (ind.frame() == 0) {
      continue;
    }

    // Queue of reachability obligations
    obligation_queue reachability_obligations;
    reachability_obligations.push(obligation(ind.frame(), G));

    // The induction not valid, try to extend to full counter-example
    while (!reachability_obligations.empty()) {

      // Get the next satisfiability obligations
      obligation reach = reachability_obligations.top();

      // Check if the obligation is reachable
      G = check_one_step_reachable(reach.frame(), reach.formula());
      if (G.is_null()) {
        // Proven, remove from obligations
        reachability_obligations.pop();
        // Add the negation of the obligation to known facts
        add_learnt(reach.frame(), tm().mk_term(expr::TERM_NOT, reach.formula()));
      } else {
        // If this is a full counterexample
        if (reach.frame() == 1) {
          // If this was the property we just disproved, we're invalid
          if (ind.formula() == P) {
            return engine::INVALID;
          }
          // We disproved the inductivity, so we go for the next one
          break;
        } else {
          assert(reach.frame() > 1);
          // New obligation to reach the counterexample
          reachability_obligations.push(obligation(reach.frame()-1, G));
        }
      }
    }
  }

  return UNKNOWN;
}

const system::state_trace* ic3_engine::get_trace() {
  return 0;
}

void ic3_engine::to_stream(std::ostream& out) const  {
  for (size_t k = 0; k < d_frame_content.size(); ++ k) {
    out << "Frame " << k << ":" << std::endl;
    formula_set::const_iterator it = d_frame_content[k].begin();
    for (; it != d_frame_content[k].end(); ++ it) {
      out << *it << std::endl;
    }
  }
}

}
}
