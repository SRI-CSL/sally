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

#include <stack>
#include <cassert>
#include <sstream>
#include <iostream>

#define unused_var(x) { (void)x; }

namespace sally {
namespace ic3 {

bool obligation_compare_induction::operator () (const obligation& o1, const obligation& o2) const {
  // Smaller frame wins
  if (o1.frame() != o2.frame()) {
    return o1.frame() > o2.frame();
  }
  // Smaller depth wins
  if (o1.depth() != o2.depth()) {
    return o1.depth() > o2.depth();
  }
  return o1.formula() > o2.formula();
}

ic3_engine::ic3_engine(const system::context& ctx)
: engine(ctx)
, d_transition_system(0)
, d_property(0)
{
}

std::ostream& operator << (std::ostream& out, const ic3_engine& ic3) {
  ic3.to_stream(out);
  return out;
}

ic3_engine::~ic3_engine() {
  for (size_t k = 0; k < d_solvers.size(); ++ k) {
    delete d_solvers[k];
  }
}

expr::term_ref ic3_engine::check_one_step_reachable(size_t k, expr::term_ref F) {
  assert(k > 0);

  // The state type
  const system::state_type* state_type = d_transition_system->get_state_type();

  // Get the solver of the previous frame
  smt::solver* solver = get_solver(k-1);
  smt::solver_scope scope(solver);

  // Add the formula (moving current -> next)
  scope.push();
  expr::term_ref F_next = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);
  solver->add(F_next, smt::solver::CLASS_B);

  // Figure out the result
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    return generalize_sat_at(k, solver);
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
  ensure_frame(k);
  ensure_frame(k+1);
  assert(!F.is_null());
  assert(d_frame_content[k].find(F) != d_frame_content[k].end());
  assert(d_frame_content[k+1].find(F) != d_frame_content[k].end());

  TRACE("ic3") << "ic3: Checking inductive at " << k << " for " << F << std::endl;

  // The state type
  const system::state_type* state_type = d_transition_system->get_state_type();

  // Get the solver of the previous frame
  smt::solver* solver = get_solver(k);
  smt::solver_scope scope(solver);

  // Add the formula (moving current -> next)
  scope.push();
  expr::term_ref F_not = tm().mk_term(expr::TERM_NOT, F);
  expr::term_ref F_not_next = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F_not);
  solver->add(F_not_next, smt::solver::CLASS_B);

  // Figure out the result
  expr::term_ref result;
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    result = generalize_sat_at(k, solver);
    break;
  }
  case smt::solver::UNSAT:
    // Unsat, we return NULL
    break;
  default:
    throw exception("SMT unknown result.");
  }

  TRACE("ic3") << "ic3: " << (result.is_null() ? "inductive" : "not inductive") << std::endl;

  return result;
}

void ic3_engine::add_valid_up_to(size_t k, expr::term_ref F) {
  TRACE("ic3") << "ic3: adding at " << k << ": " << F << std::endl;

  // Ensure frame is setup
  ensure_frame(k);

  if (k == 0) {
    // Special case for adding to 0 frame
    if (!frame_contains(0, F)) {
      d_frame_content[0].insert(F);
      get_solver(0)->add(F, smt::solver::CLASS_A);
    }
  } else {
    // Add to all frames from 1..k (not adding to 0, intiial states need no refinement)
    for(int i = k; i >= 1; -- i) {
      if (frame_contains(i, F)) {
        break;
      }
      d_frame_content[i].insert(F);
      get_solver(i)->add(F, smt::solver::CLASS_A);
    }
  }
}

void ic3_engine::add_to_induction_obligations(size_t k, expr::term_ref f, size_t depth) {
  d_induction_obligations.push(obligation(k, f, depth));
}

void ic3_engine::ensure_frame(size_t k) {
  if (d_solvers.size() <= k && output::get_verbosity(std::cout) > 0) {
    std::cout << "ic3: Extending trace to " << k << std::endl;
  }

  while (d_solvers.size() <= k) {

    // Make the solver
    smt::solver* solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
    d_solvers.push_back(solver);
    // Add the variable classes
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    solver->add_x_variables(x.begin(), x.end());
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    solver->add_y_variables(x_next.begin(), x_next.end());

    // Add the transition relation
    solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_A);
    // Add the frame content
    d_frame_content.push_back(formula_set());
    // No failed induction so far
    d_has_failed_induction.push_back(false);
  }
  assert(d_solvers.size() == d_frame_content.size());
}

bool ic3_engine::frame_contains(size_t k, expr::term_ref f) {
  ensure_frame(k);
  return d_frame_content[k].find(f) != d_frame_content[k].end();
}

bool ic3_engine::check_reachable(size_t k, expr::term_ref f) {

  TRACE("ic3") << "ic3: checking reachability at " << k << std::endl;

  // Queue of reachability obligations
  std::stack<obligation> reachability_obligations;
  reachability_obligations.push(obligation(k, f, 0));

  // We're not reachable, if we hit 0 we set it to true
  bool reachable = false;

  // The induction not valid, try to extend to full counter-example
  for (size_t check = 0; !reachability_obligations.empty(); ++ check) {
    // Get the next reachability obligations
    obligation reach = reachability_obligations.top();
    // If we're at 0 frame, we're reachable anything passed in is consistent
    // part of the abstraction
    if (reach.frame() == 0) {
      reachable = true;
      break;
    }
    // Check if the obligation is reachable
    expr::term_ref G = check_one_step_reachable(reach.frame(), reach.formula());
    if (G.is_null()) {
      // Proven, remove from obligations
      reachability_obligations.pop();
      // Learn
      if (reach.frame() < k) {
        // Learn something at k that refutes the formula
        expr::term_ref learnt = learn_forward(reach.frame(), reach.formula());
        // Add any unreachability learnts, but not f itself
        add_valid_up_to(reach.frame(), learnt);
      }
    } else {
      // New obligation to reach the counterexample
      reachability_obligations.push(obligation(reach.frame()-1, G, 0));
    }
  }

  TRACE("ic3") << "ic3: " << (reachable ? "reachable" : "not reachable") << std::endl;

  // All discharged, so it's not reachable
  return reachable;
}

bool ic3_engine::check_valid_and_add(size_t k, expr::term_ref f, size_t depth) {

  if (output::get_verbosity(std::cout) > 0) {
     std::cout << "ic3: checking validity" << std::endl;
  }

  ensure_frame(k);

  expr::term_ref f_not = tm().mk_term(expr::TERM_NOT, f);
  smt::solver* solver = get_solver(k);
  solver->push();
  solver->add(f_not, smt::solver::CLASS_A);
  smt::solver::result r = solver->check();
  solver->pop();
  switch (r) {
  case smt::solver::SAT:
    // Invalid, property is not valid
    return false;
  case smt::solver::UNSAT:
    // Valid, we continue with P
    add_valid_up_to(k, f);
    return true;
  default:
    throw exception("Unknown SMT result.");
  }
}

expr::term_ref ic3_engine::learn_forward(size_t k, expr::term_ref G) {


  TRACE("ic3") << "learning forward to refute: " << G << std::endl;

  assert(k > 0);

  // If we don't have interpolation, just learn not G
  if (!get_solver(k-1)->supports(smt::solver::INTERPOLATION)) {
    return tm().mk_term(expr::TERM_NOT, G);
  }

  // Get the interpolant I1 for: (R_{k-1} and T => I1, I1 and G unsat
  smt::solver* I1_solver = get_solver(k-1);
  I1_solver->push();
  expr::term_ref G_next = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, G);
  I1_solver->add(G_next, smt::solver::CLASS_B);
  smt::solver::result I1_result = I1_solver->check();
  unused_var(I1_result);
  assert(I1_result == smt::solver::UNSAT);
  expr::term_ref I1 = I1_solver->interpolate();
  I1 = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_NEXT, system::state_type::STATE_CURRENT, I1);
  I1_solver->pop();

  TRACE("ic3") << "I1: " << I1 << std::endl;

  // Get the interpolant I2 for I => I2, I2 and G unsat
  smt::solver* I2_solver = get_solver(0);
  I2_solver->push();
  I2_solver->add(G, smt::solver::CLASS_B);
  smt::solver::result I2_result = I2_solver->check();
  unused_var(I2_result);
  assert(I2_result == smt::solver::UNSAT);
  expr::term_ref I2 = I2_solver->interpolate();
  I2_solver->pop();

  TRACE("ic3") << "I2: " << I2 << std::endl;

  // Result is the disjunction of the two
  expr::term_ref learnt = tm().mk_term(expr::TERM_OR, I1, I2);

  return learnt;
}

bool ic3_engine::push_if_inductive(size_t k, expr::term_ref f, size_t depth) {

  ensure_frame(k);
  ensure_frame(k+1);

  std::vector<expr::term_ref> induction_assumptions;

  TRACE("ic3") << "ic3: pushing at " << k << ":" << f << std::endl;

  bool inductive = false;
  for (size_t check = 0; ; check ++) {

    // Check if inductive
    expr::term_ref G = check_inductive_at(k, f);

    // If inductive
    if (G.is_null()) {
      inductive = true;
      break;
    }

    // We have a counterexample, we only try to refute if induction depth is not
    // exceeded
    if (depth > k) {
      inductive = false;
      break;
    }

    // Check if G is reachable
    bool reachable = check_reachable(k, G);

    // If reachable, we're not inductive
    if (reachable) {
      inductive = false;
      break;
    }

    // Learn something to refute G
    expr::term_ref learnt = learn_forward(k, G);
    TRACE("ic3") << "ic3: learnt: " << learnt << std::endl;

    // Add the learnt
    add_valid_up_to(k, learnt);
    induction_assumptions.push_back(learnt);
  }

  // If inductive, add the assumptions to induction obligations
  if (inductive) {
    TRACE("ic3") << "ic3: proved at " << k << " with " << induction_assumptions.size() << " assumptions" << std::endl;
    // Add the thing we learnt
    add_valid_up_to(k+1, f);
    add_to_induction_obligations(k+1, f, depth);
    for (size_t i = 0; i < induction_assumptions.size(); ++ i) {
      add_to_induction_obligations(k, induction_assumptions[i], depth+1);
    }
  }

  return inductive;
}

engine::result ic3_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Remember the input
  d_transition_system = ts;
  d_property = sf;

  // Add the initial state
  expr::term_ref I = d_transition_system->get_initial_states();
  add_valid_up_to(0, I);
  add_to_induction_obligations(0, I, 0);

  // Add the property we're trying to prove
  expr::term_ref P = d_property->get_formula();
  bool P_valid = check_valid_and_add(0, P, 0);
  if (!P_valid) {
    return engine::INVALID;
  } else {
    add_to_induction_obligations(0, P, 0);
  }

  // Search while we have something to do
  while (!d_induction_obligations.empty()) {

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    obligation ind = d_induction_obligations.top();
    d_induction_obligations.pop();

    // If already ahead, we'll prove it there
    assert(!frame_contains(ind.frame()+1, ind.formula()));

    /** Push the formula forward if it's inductive at the frame */
    bool is_inductive = push_if_inductive(ind.frame(), ind.formula(), ind.depth());
    if (!is_inductive) {
      // Not inductive, if P then we have a counterexample
      if (ind.formula() == P) {
        return engine::INVALID;
      } else {
        d_has_failed_induction[ind.frame()] = true;
      }
    } else {
      // Inductive, if frames equal, we have a proofs
      if (!d_has_failed_induction[ind.frame()] && d_frame_content[ind.frame()].size() == d_frame_content[ind.frame()+1].size()) {
        if (ctx().get_options().get_bool("ic3-show-invariant")) {
          print_frame(ind.frame(), std::cout);
        }
        return engine::VALID;
      }
    }
  }

  // Didn't prove or disprove, so unknown
  return engine::UNKNOWN;
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

smt::solver* ic3_engine::get_solver(size_t k) {
  ensure_frame(k);
  return d_solvers[k];
}

void ic3_engine::print_frames(std::ostream& out) const {
  for (size_t k = 0; k < d_frame_content.size(); ++ k) {
    print_frame(k, out);
  }
}

void ic3_engine::print_frame(size_t k, std::ostream& out) const {
  out << tm().mk_and(d_frame_content[k]) << std::endl;
}

expr::term_ref ic3_engine::generalize_sat_at(size_t k, smt::solver* solver) {
  std::vector<expr::term_ref> generalization_facts;
  solver->generalize(generalization_facts);
  return tm().mk_and(generalization_facts);
}

}
}
