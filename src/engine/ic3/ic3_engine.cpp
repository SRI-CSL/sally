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
#include "expr/gc_relocator.h"

#include <stack>
#include <cassert>
#include <sstream>
#include <iostream>

#define unused_var(x) { (void)x; }

namespace sally {
namespace ic3 {

/** A reachability obligation at frame k. */
class reachability_obligation {

  /** The frame of the obligation */
  size_t d_k;
  /** The forumula in question */
  expr::term_ref d_P;

public:

  /** Construct the obligation */
  reachability_obligation(size_t k, expr::term_ref P)
  : d_k(k), d_P(P){}

  /** Get the frame */
  size_t frame() const { return d_k; }

  /** Get the formula */
  expr::term_ref formula() const { return d_P; }

};

ic3_engine::ic3_engine(const system::context& ctx)
: engine(ctx)
, d_transition_system(0)
, d_property(0)
, d_reachability_solver(0)
, d_induction_solver(0)
, d_counterexample_solver(0)
, d_counterexample_solver_depth(0)
, d_trace(0)
, d_induction_frame(0)
{
  for (size_t i = 0; i < 10; ++ i) {
    std::stringstream ss;
    ss << "sally::ic3::frame_size[" << i << "]";
    utils::stat_int* s = new utils::stat_int(ss.str(), 0);
    d_stat_frame_size.push_back(s);
    ctx.get_statistics().add(s);
  }
}

std::ostream& operator << (std::ostream& out, const ic3_engine& ic3) {
  ic3.to_stream(out);
  return out;
}

ic3_engine::~ic3_engine() {
  for (size_t k = 0; k < d_solvers.size(); ++ k) {
    delete d_solvers[k];
  }
  delete d_reachability_solver;
  delete d_induction_solver;
  delete d_counterexample_solver;
  delete d_trace;
}

expr::term_ref ic3_engine::check_one_step_reachable(size_t k, expr::term_ref F) {
  assert(k > 0);

  // The state type
  const system::state_type* state_type = d_transition_system->get_state_type();

  // Move the formula variables current -> next
  expr::term_ref F_next = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);

  // Query
  return query_at(k-1, F_next, smt::solver::CLASS_B);
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
  assert(k > 0);

  // Ensure frame is setup
  ensure_frame(k);
  // Add to all frames from 1..k (not adding to 0, initial states need no refinement)
  for(int i = k; i >= 1; -- i) {
    if (frame_contains(i, F)) {
      break;
    }
    add_to_frame(i, F);
  }
}

induction_obligation ic3_engine::pop_induction_obligation() {
  assert(d_induction_obligations.size() > 0);
  induction_obligation ind = d_induction_obligations.top();
  d_induction_obligations.pop();
  return ind;
}

void ic3_engine::init_solver(size_t k) {

  if (ctx().get_options().get_bool("ic3-single-solver")) {

    // The variables from the state type
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);

    // Add the reachability solver
    if (d_reachability_solver == 0) {
      d_reachability_solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
      d_reachability_solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
      d_reachability_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
      d_reachability_solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
    }

    // Add the induction solver
    if (d_induction_solver == 0) {
      d_induction_solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
      d_induction_solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
      d_induction_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
      d_induction_solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
    }
  } else {
    if (d_solvers.size() <= k) {
      d_solvers.resize(k+1, 0);
    }
    assert(d_solvers[k] == 0);
    smt::solver* solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
    d_solvers[k] = solver;
    // Add the variable classes
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
    // Add the transition relation
    solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
  }

}

void ic3_engine::ensure_frame(size_t k) {

  if (d_solvers.size() <= k) {
    MSG(1) << "ic3: Extending trace to " << k << std::endl;
  }

  // Upsize the solvers and frames if necessary
  while (d_frame_content.size() <= k) {

    // Make the solver
    init_solver(d_frame_content.size());

    // Add the empty frame content
    d_frame_content.push_back(formula_set());
    // Number of obligations per frame
    d_induction_obligations_count.push_back(0);

    // Add transition relation k -> k + 1 to the counter-example solver
    expr::term_ref T = d_trace->get_transition_formula(d_transition_system->get_transition_relation(), k, k + 1);
    get_counterexample_solver()->add(T, smt::solver::CLASS_A);
    d_counterexample_solver_depth ++;
  }

}

void ic3_engine::restart_solvers() {

  if (d_frame_content.size() < 2) {
    // Nothing to reduce
    return;
  }

  MSG(1) << "ic3: restarting solvers" << std::endl;

  // Restart the solvers from frames 1..last
  for (size_t k = 0; k <= d_induction_frame; ++ k) {

    // Restart the solver
    delete d_solvers[k];
    d_solvers[k] = 0;
    init_solver(k);

    // Add the content again
    formula_set::const_iterator it = d_frame_content[k].begin();
    for (; it != d_frame_content[k].end(); ++ it) {
      d_solvers[k]->add(*it, smt::solver::CLASS_A);
    }
  }
}

bool ic3_engine::frame_contains(size_t k, expr::term_ref f) {
  ensure_frame(k);
  return d_frame_content[k].find(f) != d_frame_content[k].end();
}

bool ic3_engine::check_reachable(size_t k, expr::term_ref f) {

  TRACE("ic3") << "ic3: checking reachability at " << k << std::endl;

  // Queue of reachability obligations
  std::vector<reachability_obligation> reachability_obligations;
  reachability_obligations.push_back(reachability_obligation(k, f));

  // We're not reachable, if we hit 0 we set it to true
  bool reachable = false;

  // The induction not valid, try to extend to full counter-example
  for (size_t check = 0; !reachability_obligations.empty(); ++ check) {
    // Get the next reachability obligations
    reachability_obligation reach = reachability_obligations.back();
    // If we're at 0 frame, we're reachable: anything passed in is consistent
    // part of the abstraction
    if (reach.frame() == 0) {
      // We're reachable, mark it
      reachable = true;
      // Remember the counterexample
      d_counterexample.clear();
      for (size_t i = 0; i < reachability_obligations.size(); ++ i) {
        d_counterexample.push_front(reachability_obligations[i].formula());
      }
      break;
    }

    // Check if the obligation is reachable
    expr::term_ref G = check_one_step_reachable(reach.frame(), reach.formula());
    if (G.is_null()) {
      // Proven, remove from obligations
      reachability_obligations.pop_back();
      // Learn
      if (reach.frame() < k) {
        // Learn something at k that refutes the formula
        expr::term_ref learnt = learn_forward(reach.frame(), reach.formula());
        // Add any unreachability learnts, but not f itself
        add_valid_up_to(reach.frame(), learnt);
      }
    } else {
      // New obligation to reach the counterexample
      reachability_obligations.push_back(reachability_obligation(reach.frame()-1, G));
    }
  }

  TRACE("ic3") << "ic3: " << (reachable ? "reachable" : "not reachable") << std::endl;

  // All discharged, so it's not reachable
  return reachable;
}

bool ic3_engine::check_valid(size_t k, expr::term_ref f) {

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
    return true;
  default:
    throw exception("Unknown SMT result.");
  }
}

expr::term_ref ic3_engine::eq_to_ineq(expr::term_ref G) {

  std::vector<expr::term_ref> G_new;

  // Get the conjuncts
  const expr::term& G_term = tm().term_of(G);
  if (G_term.op() != expr::TERM_AND) { return G; }
  for (size_t i = 0; i < G_term.size(); ++ i) {
    const expr::term& t = tm().term_of(G_term[i]);
    expr::term_ref lhs = t[0];
    expr::term_ref rhs = t[1];
    if (t.op() == expr::TERM_EQ && tm().is_subtype_of(tm().type_of(lhs), tm().real_type())) {
      G_new.push_back(tm().mk_term(expr::TERM_LEQ, lhs, rhs));
      G_new.push_back(tm().mk_term(expr::TERM_GEQ, lhs, rhs));
    } else {
      G_new.push_back(G_term[i]);
    }
  }

  return tm().mk_and(G_new);
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

ic3_engine::induction_result ic3_engine::push_if_inductive(const induction_obligation& ind) {

  size_t depth = ind.depth();
  expr::term_ref f = ind.formula();

  ensure_frame(d_induction_frame);
  assert(frame_contains(d_induction_frame, f));

  TRACE("ic3") << "ic3: pushing at " << d_induction_frame << ":" << f << std::endl;

  // Check if inductive
  expr::term_ref G = check_inductive_at(d_induction_frame, f);

  TRACE("ic3::generalization") << "ic3: generalization " << G << std::endl;

  // If inductive
  if (G.is_null()) {
    // Add to the next frame
    d_induction_obligations_next.insert(induction_obligation(f, depth, ind.score()));
    return INDUCTION_SUCCESS;
  }

  // We have a counterexample, we only try to refute if induction depth is not
  // exceeded
  if (!ctx().get_options().get_bool("ic3-no-depth-bound") && depth > d_induction_frame) {
    return INDUCTION_INCONCLUSIVE;
  }

  // Check if G is reachable
  bool reachable = check_reachable(d_induction_frame, G);

  // If reachable, we're not inductive
  if (reachable) {
    return INDUCTION_FAIL;
  }

  // Learn something to refute G
  expr::term_ref learnt = learn_forward(d_induction_frame, G);
  TRACE("ic3") << "ic3: learnt: " << learnt << std::endl;

  // Add the learnt
  add_valid_up_to(d_induction_frame, learnt);

  // Add to obligations if not already shown invalid
  if (!d_frame_formula_info[learnt].invalid) {
    // Try to push assumptions next time
    d_induction_obligations.push(induction_obligation(learnt, depth+1, 0));
    d_frame_formula_info[learnt] = frame_formula_info(f, G);
  }

  return INDUCTION_RETRY;
}

void ic3_engine::add_to_frame(size_t k, expr::term_ref f) {
  ensure_frame(k);
  assert(d_frame_content[k].count(f) == 0);

  // Add appropriately
  if (ctx().get_options().get_bool("ic3-single-solver")) {
    // Add te enabling variable and the implication to enable the assertion
    expr::term_ref assertion = tm().mk_term(expr::TERM_IMPLIES, get_frame_variable(k), f);
    d_reachability_solver->add(assertion, smt::solver::CLASS_A);
    // If at induction frame, add to induction solver
    if (k == d_induction_frame) {
      d_induction_solver->add(assertion, smt::solver::CLASS_A);
    }
  } else {
    // Add directly
    get_solver(k)->add(f, smt::solver::CLASS_A);
  }


  // Remember
  d_frame_content[k].insert(f);
  if (k < d_stat_frame_size.size()) {
    d_stat_frame_size[k]->get_value() ++;
  }
}

void ic3_engine::check_deadlock() {
  for (size_t k = 0; k < d_solvers.size(); ++ k) {
    smt::solver* solver = get_solver(k);
    smt::solver::result result = solver->check();
    if (result == smt::solver::UNSAT) {
      std::stringstream ss;
      ss << "Solver " << k << " is inconsistent!";
      throw exception(ss.str());
    }
  }
}

template<typename T>
class scoped_value {
  T& d_variable;
  T d_old_value;
public:
  scoped_value(T& variable)
  : d_variable(variable)
  , d_old_value(variable) {}
  ~scoped_value() {
    d_variable = d_old_value;
  }
};

void ic3_engine::extend_induction_failure(expr::term_ref f) {

  assert(d_counterexample.size() > 0);

  // We have a counter-example to inductiveness of f at at pushing frame
  // and d_counterexample has its generalization at the back.
  assert(d_counterexample.size() == d_induction_frame + 1);

  // Solver for checking
  smt::solver* solver = get_counterexample_solver();
  smt::solver_scope solver_scope(solver);
  solver_scope.push();
  scoped_value<size_t> depth_scope(d_counterexample_solver_depth);

  // Assert all the generalizations
  size_t k = 0;
  for (; k < d_counterexample.size(); ++ k) {
    // Add the generalization to frame k
    expr::term_ref G_k = d_trace->get_state_formula(d_counterexample[k], k);
    solver->add(G_k, smt::solver::CLASS_A);
  }

  // Try to extend it
  for (;; ++ k) {

    // We know there is a counterexample to induction of f: 0, ..., k, with f
    // being false a k + 1.
    assert(d_frame_formula_info[f].invalid == true);
    // We have enough transitions to reach k + 1
    assert(k + 1 == d_counterexample_solver_depth);

    expr::term_ref G = d_frame_formula_info[f].refutes;
    expr::term_ref parent = d_frame_formula_info[f].parent;

    // If no more parents, we're done
    if (parent.is_null()) {
      break;
    }

    // Add to next
    expr::term_ref G_k = d_trace->get_state_formula(G, k);
    solver->add(G_k, smt::solver::CLASS_A);

    // If not a generalization, must check to see if we're reachable
    if (f != tm().mk_term(expr::TERM_NOT, G)) {
      // If not a generalization we need to check
      smt::solver::result r = solver->check();

      // If not sat, we can't extend any more
      if (r != smt::solver::SAT) {
        break;
      }
    }

    // We're sat (either by knowing, or by checking), so we extend further
    f = parent;
    d_frame_formula_info[f].invalid = true;
    d_counterexample.push_back(G);

    // One more transition relation
    expr::term_ref T_k = d_trace->get_transition_formula(d_transition_system->get_transition_relation(), k, k + 1);
    d_counterexample_solver_depth ++;
    solver->add(T_k, smt::solver::CLASS_A);
  }
}

void ic3_engine::push_current_frame() {

  expr::term_ref property = d_property->get_formula();

  // Search while we have something to do
  while (!d_induction_obligations.empty() && !d_frame_formula_info[property].invalid ) {

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    induction_obligation ind = pop_induction_obligation();

    // If formula or one of its parents is marked as invalid, skip it
    if (d_frame_formula_info[ind.formula()].invalid) {
      continue;
    }

    // Push the formula forward if it's inductive at the frame
    size_t old_total = total_facts();
    induction_result ind_result = push_if_inductive(ind);
    ind.add_score(total_facts() - old_total);

    // See what happened
    switch (ind_result) {
    case INDUCTION_RETRY:
      // We'll retry the same formula (it's already added to the solver)
      d_induction_obligations.push(ind);
      break;
    case INDUCTION_SUCCESS:
      // Boss
      break;
    case INDUCTION_FAIL:
      // Not inductive, mark it
      d_frame_formula_info[ind.formula()].invalid = true;
      // Try to extend the counter-example further
      extend_induction_failure(ind.formula());
      break;
    case INDUCTION_INCONCLUSIVE:
      break;
    }

  }
}

engine::result ic3_engine::search() {

  // Push frame by frame */
  for(;;) {

    // Push the current induction frame forward
    push_current_frame();

    // If we've disproved the property, we're done
    if (d_frame_formula_info[d_property->get_formula()].invalid) {
      return engine::INVALID;
    }

    // If we pushed all of them, we're done
    if (d_frame_content[d_induction_frame].size() == d_induction_obligations_next.size()) {
      if (ctx().get_options().get_bool("ic3-show-invariant")) {
        print_frame(d_induction_frame, std::cout);
      }
      return engine::VALID;
    }

    // Move to the next frame
    d_induction_frame ++;
    d_induction_obligations.clear();
    if (ctx().get_options().get_bool("ic3-single-solver")) {
      // Reset the induction solver
      delete d_induction_solver;
      init_solver(d_induction_frame);
    }

    std::set<induction_obligation>::const_iterator it = d_induction_obligations_next.begin();
    for (; it != d_induction_obligations_next.end(); ++ it) {
      // Push if not shown invalid
      if (!d_frame_formula_info[it->formula()].invalid) {
        add_to_frame(d_induction_frame, it->formula());
        d_induction_obligations.push(*it);
      }
    }
    d_induction_obligations_next.clear();

    // Do garbage collection
    gc_solvers();

    // Restart if asked
    if (ctx().get_options().get_bool("ic3-enable-restarts")) {
      return engine::UNKNOWN;
    }
  }

  // Didn't prove or disprove, so unknown
  return engine::UNKNOWN;
}


void ic3_engine::reset() {

  d_transition_system = 0;
  d_property = 0;
  for (size_t i = 0; i < d_solvers.size(); ++ i) {
    delete d_solvers[i];
  }
  d_solvers.clear();
  delete d_counterexample_solver;
  d_counterexample_solver_depth = 0;
  d_counterexample.clear();
  delete d_trace;
  d_trace = 0;
  d_induction_frame = 0;
  d_induction_obligations.clear();
  d_induction_obligations_next.clear();
  d_induction_obligations_count.clear();
  d_frame_content.clear();
  for (size_t i = 0; i < d_stat_frame_size.size(); ++ i) {
    d_stat_frame_size[i]->get_value() = 0;
  }
}

engine::result ic3_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Initialize
  result r = UNKNOWN;
  d_induction_frame = 0;

  // Reset the solver
  reset();

  // Remember the input
  d_transition_system = ts;
  d_property = sf;

  // Make the trace
  d_trace = new system::state_trace(sf->get_state_type());

  // Start with at least one frame
  ensure_frame(0);

  // Add the initial state
  expr::term_ref I = d_transition_system->get_initial_states();
  add_to_frame(0, I);
  d_induction_obligations.push(induction_obligation(I, 0, 0));

  // Add the property we're trying to prove
  expr::term_ref P = d_property->get_formula();
  bool P_valid = check_valid(0, P);
  if (!P_valid) {
    return engine::INVALID;
  } else {
    add_to_frame(0, P);
    d_induction_obligations.push(induction_obligation(P, 0, 0));
  }

  while (r == UNKNOWN) {

    MSG(1) << "ic3: starting search" << std::endl;

    // Search
    r = search();

    // Reduce learnts
    if (r == UNKNOWN) {
      restart_solvers();
    }
  }

  return r;
}

const system::state_trace* ic3_engine::get_trace() {

  // Add the property to the end of the counterexample
  d_counterexample.push_back(tm().mk_term(expr::TERM_NOT, d_property->get_formula()));
  d_trace->resize_to(d_counterexample.size());

  smt::solver* solver = get_counterexample_solver();
  smt::solver_scope solver_scope(solver);
  solver_scope.push();

  std::vector<expr::term_ref> all_variables;

  // The transition relation
  expr::term_ref T = d_transition_system->get_transition_relation();

  // Assert neede stuff
  for (size_t k = 0; k < d_counterexample.size(); ++ k) {
    // Get the variable to add to solver
    d_trace->get_state_variables(k, all_variables);
    // If not added already, add the transition relation
    if (k >= d_counterexample_solver_depth && k + 1 < d_counterexample.size()) {
      expr::term_ref T_k = d_trace->get_transition_formula(T, k, k + 1);
      solver->add(T_k, smt::solver::CLASS_A);
    }
    // Add the counter-example part
    expr::term_ref G = d_counterexample[k];
    expr::term_ref G_k = d_trace->get_state_formula(G, k);
    solver->add(G_k, smt::solver::CLASS_A);
  }

  // Check
  solver->add_variables(all_variables.begin(), all_variables.end(), smt::solver::CLASS_A);
  smt::solver::result r = solver->check();
  unused_var(r);
  assert(r == smt::solver::SAT);

  // Get the model
  expr::model m(tm(), true);
  solver->get_model(m);

  // Set the model to the trace
  d_trace->add_model(m);

  return d_trace;
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
  assert(!ctx().get_options().get_bool("ic3-single-solver"));
  return d_solvers[k];
}

smt::solver* ic3_engine::get_counterexample_solver() {
  if (d_counterexample_solver == 0) {
    assert(d_induction_frame == 0);
    d_counterexample_solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
    expr::term_ref I0 = d_trace->get_state_formula(d_transition_system->get_initial_states(), 0);
    d_counterexample_solver->add(I0, smt::solver::CLASS_A);
    d_counterexample_solver_depth = 0;
  }
  return d_counterexample_solver;
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
  solver->generalize(smt::solver::GENERALIZE_BACKWARD, generalization_facts);

  // Remove anything already known at the frame
  size_t to_keep = 0;
  for (size_t i = 0; i < generalization_facts.size(); ++ i) {
    if (!frame_contains(k, generalization_facts[i])) {
      generalization_facts[to_keep++] = generalization_facts[i];
    }
  }
  generalization_facts.reserve(to_keep);

  expr::term_ref G = tm().mk_and(generalization_facts);
  G = eq_to_ineq(G);
  return G;
}

size_t ic3_engine::total_facts() const {
  // Frames are smaller and smaller, so we return the first one. But, since we
  // never add to frame 0, we return frame 0 + frame 1
  assert (d_frame_content.size() > 0);
  if (d_frame_content.size() > 1) {
    return d_frame_content[0].size() + d_frame_content[1].size();
  } else {
    return d_frame_content[0].size();
  }
}

void ic3_engine::gc_solvers() {
  for (size_t i = 0; i < d_solvers.size(); ++ i) {
    d_solvers[i]->gc();
  }
  d_counterexample_solver->gc();
}

void ic3_engine::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_counterexample);
  d_frame_formula_info.reloc(gc_reloc);
  assert(d_induction_obligations_next.size() == 0);
  for (size_t i = 0; i < d_frame_content.size(); ++ i) {
    gc_reloc.reloc(d_frame_content[i]);
  }
  gc_reloc.reloc(d_frame_variables);
}

expr::term_ref ic3_engine::query_at(size_t k, expr::term_ref f, smt::solver::formula_class f_class) {

  smt::solver* solver = 0;
  if (ctx().get_options().get_bool("ic3-single-solver")) {
    solver = d_reachability_solver;
  } else {
    solver = get_solver(k);
  }
  smt::solver_scope scope(solver);

  // Add the formula (moving current -> next)
  scope.push();
  solver->add(f, f_class);

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

expr::term_ref ic3_engine::get_frame_variable(size_t i) {
  while (d_frame_variables.size() <= i) {
    std::stringstream ss;
    ss << "frame_" << i;
    expr::term_ref var = tm().mk_variable(ss.str(), tm().boolean_type());
    d_frame_variables.push_back(var);
  }
  return d_frame_variables[i];
}

}
}
