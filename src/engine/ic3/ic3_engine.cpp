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
  delete d_trace;
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
  assert(k > 0);

  // Ensure frame is setup
  ensure_frame(k);
  // Add to all frames from 1..k (not adding to 0, intiial states need no refinement)
  for(int i = k; i >= 1; -- i) {
    if (frame_contains(i, F)) {
      break;
    }
    add_to_frame(i, F);
    if (output::trace_tag_is_enabled("ic3::deadlock")) {
      smt::solver::result r = get_solver(i)->check();
      if (r != smt::solver::SAT) {
        throw exception("Solver in inconsistent state");
      }
    }

  }
}

induction_obligation ic3_engine::pop_induction_obligation() {
  assert(d_induction_obligations.size() > 0);
  induction_obligation ind = d_induction_obligations.top();
  d_induction_obligations.pop();
  return ind;
}

void ic3_engine::init_solver(size_t k) {
  assert(k < d_solvers.size());
  assert(d_solvers[k] == 0);
  smt::solver* solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
  d_solvers[k] = solver;
  // Add the variable classes
  const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
  solver->add_x_variables(x.begin(), x.end());
  const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
  solver->add_y_variables(x_next.begin(), x_next.end());
  // Add the transition relation
  solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
}

void ic3_engine::ensure_frame(size_t k) {
  if (d_solvers.size() <= k) {
    MSG(1) << "ic3: Extending trace to " << k << std::endl;
  }

  while (d_solvers.size() <= k) {
    // Make the solver
    size_t i = d_solvers.size();
    d_solvers.push_back(0);
    init_solver(i);

    // Add the empty frame content
    d_frame_content.push_back(formula_set());
    // Number of obligations per frame
    d_induction_obligations_count.push_back(0);
  }
}

size_t ic3_engine::get_score(expr::term_ref f) const {
  formula_scores_map::const_iterator find = d_formula_scores.find(f);
  if (find == d_formula_scores.end()) {
    return 0;
  } else {
    return find->second;
  }
}

void ic3_engine::reduce_learnts() {

  if (d_frame_content.size() < 2) {
    // Nothing to reduce
    return;
  }

  bool agressive = ctx().get_options().get_bool("ic3-aggresive-reduce");

  MSG(1) << "ic3: reducing learnts" << std::endl;

  std::vector<expr::term_ref> to_remove;
  std::copy(d_frame_content[1].begin(), d_frame_content[1].end(), std::back_inserter(to_remove));

  // Frame with the content
  size_t last_frame = d_frame_content.size() - 1;

  // We don't remove the last frame
  if (!agressive) {
    size_t to_keep_in_remove = 0;
    for (size_t i = 0; i < to_remove.size(); ++i) {
      if (d_frame_content[last_frame].count(to_remove[i]) == 0) {
        // We keep this one in to_remove
        to_remove[to_keep_in_remove++] = to_remove[i];
      }
    }
    to_remove.resize(to_keep_in_remove);
  }

  // Sort removables by increasing score
  learnt_cmp cmp(d_formula_scores);
  std::sort(to_remove.begin(), to_remove.end(), cmp);
  assert(get_score(to_remove[0]) <= get_score(to_remove.back()));

  // If no score, remove all, otherwise half
  size_t median = get_score(to_remove[to_remove.size()/2]);

  // Remove the first solver
  delete d_solvers[0];
  d_solvers[0] = 0;
  init_solver(0);
  d_solvers[0]->add(d_transition_system->get_initial_states(), smt::solver::CLASS_A);

  // Remove the from frames 1..last
  for (size_t k = 1; k < last_frame; ++ k) {

    // Remove the frame content
    for (size_t i = 0; i < to_remove.size(); ++ i) {
      expr::term_ref f = to_remove[i];
      if (get_score(f) <= median) {
        d_frame_content[k].erase(f);
      }
    }

    // Update the stats
    if (k < d_stat_frame_size.size()) {
      d_stat_frame_size[k]->get_value() = d_frame_content[k].size();
    }

    // Reboot the solver
    delete d_solvers[k];
    d_solvers[k] = 0;
    init_solver(k);

    // Add the content again
    formula_set::const_iterator it = d_frame_content[k].begin();
    for (; it != d_frame_content[k].end(); ++ it) {
      d_solvers[k]->add(*it, smt::solver::CLASS_A);
    }
  }

   // Keep obligations
  induction_obligation_queue new_obligations;
  induction_obligation_queue::iterator ind_it = d_induction_obligations.begin();
  for (; ind_it != d_induction_obligations.end(); ++ind_it) {
    // Keep the obligation if (a) if it's the property itself or (c) if it has a good score
    if (ind_it->formula() == d_property->get_formula() || get_score(ind_it->formula()) > median) {
      induction_obligation new_obligation(ind_it->formula(), 0, get_score(ind_it->formula()));
      new_obligations.push(*ind_it);
      assert(frame_contains(last_frame, ind_it->formula()));
    }
  }
  d_induction_obligations.swap(new_obligations);

  // Clear the scores
  d_formula_scores.clear();
}


bool ic3_engine::learnt_cmp::operator () (expr::term_ref f1, expr::term_ref f2) const {
  formula_scores_map::const_iterator f1_find = scores.find(f1);
  formula_scores_map::const_iterator f2_find = scores.find(f2);
  if (f1_find == f2_find) {
    // Both out, or same
    return f1 < f2;
  }
  if (f1_find == scores.end()) {
    // Other has a score, 0 is smaler
    return true;
  }
  if (f2_find == scores.end()) {
    // First has a score, 0 is smaller
    return false;
  }
  // Same score, break tie
  if (f1_find->second == f2_find->second) {
    return f1 < f2;
  }
  // Different scores, compare
  return f1_find->second < f2_find->second;
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

expr::term_ref ic3_engine::weaken(expr::term_ref F, expr::model& m, weakening_mode mode) {

  // WEAK_FORWARD => F_is false
  assert(mode != WEAK_FORWARD || m.is_false(F));
  // WEAK_BACKWARD => F is true
  assert(mode != WEAK_BACKWARD || m.is_true(F));

  size_t F_size = tm().term_of(F).size();
  expr::term_op F_op = tm().term_of(F).op();

  expr::term_ref F_weak;

  expr::term_ref t_false = tm().mk_boolean_constant(false);
  expr::term_ref t_true = tm().mk_boolean_constant(true);

  switch (F_op) {
  case expr::TERM_AND: {
    if (mode == WEAK_FORWARD) {
      // Get the first false one
      for (size_t i = 0; i < F_size; ++i) {
        expr::term_ref child = tm().term_of(F)[i];
        if (m.get_term_value(child) == t_false) {
          // Just kee this one
          F_weak = weaken(child, m, WEAK_FORWARD);
          break;
        }
      }
    } else {
      // Weaken the conjunction
      std::vector<expr::term_ref> children;
      for (size_t i = 0; i < F_size; ++ i) {
        expr::term_ref child = tm().term_of(F)[i];
        children.push_back(weaken(child, m, WEAK_BACKWARD));
      }
      F_weak = tm().mk_and(children);
    }
    break;
  }
  case expr::TERM_OR: {
    if (mode == WEAK_FORWARD) {
      // Weaken the disjunction
      std::vector<expr::term_ref> children;
      for (size_t i = 0; i < F_size; ++ i) {
        expr::term_ref child = tm().term_of(F)[i];
        children.push_back(weaken(child, m, WEAK_FORWARD));
      }
      F_weak = tm().mk_or(children);
    } else {
      // Get the first true one
      for (size_t i = 0; i < F_size; ++i) {
        expr::term_ref child = tm().term_of(F)[i];
        if (m.get_term_value(child) == t_true) {
          // Just keep this one
          F_weak = weaken(child, m, WEAK_BACKWARD);
          break;
        }
      }
    }
    break;
  }
  case expr::TERM_NOT: {
    expr::term_ref child = tm().term_of(F)[0];
    if (mode == WEAK_FORWARD) {
      // (not F) => W(F)
      // (not W(F)) => F
      F_weak = tm().mk_term(expr::TERM_NOT, weaken(child, m, WEAK_BACKWARD));
    } else {
      // WEAK_BACKWARD
      // (not W(F) => (not F)
      // F => W(F)
      F_weak = tm().mk_term(expr::TERM_NOT, weaken(child, m, WEAK_FORWARD));
    }
    break;
  }
  case expr::TERM_EQ: {
    F_weak = F;
    if (mode == WEAK_FORWARD) {
      expr::term_ref c1 = tm().term_of(F)[0];
      expr::term_ref c1_type = tm().type_of(c1);
      if (tm().is_subtype_of(c1_type, tm().real_type())) {
        // (x = y) => x >= y and x <= y, so we pick the one that is false
        expr::term_ref c2 = tm().term_of(F)[1];
        expr::rational c1_value(tm(), m.get_term_value(c1));
        expr::rational c2_value(tm(), m.get_term_value(c2));
        if (c1_value < c2_value) {
          F_weak = tm().mk_term(expr::TERM_GEQ, c1, c2);
        } else {
          assert(c1_value > c2_value);
          F_weak = tm().mk_term(expr::TERM_LEQ, c1, c2);
        }
      }
    }
  }
  break;
  default:
    F_weak = F;
  }

  assert(!F_weak.is_null());

  // WEAK_FORWARD => F_weak is false
  assert(mode != WEAK_FORWARD || m.is_false(F_weak));
  // WEAK_BACKWARD => F_weak is true
  assert(mode != WEAK_BACKWARD || m.is_true(F_weak));

  return F_weak;
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

  // Get a model for G in R_k (only if weakening). Default values for undefined.
  expr::model G_model(tm(), true);
  if (ctx().get_options().get_bool("ic3-use-weakening")) {
    smt::solver* solver_k = get_solver(k);
    solver_k->push();
    solver_k->add(G, smt::solver::CLASS_A);
    smt::solver::result result_k = solver_k->check();
    unused_var(result_k);
    assert(result_k == smt::solver::SAT);
    solver_k->get_model(G_model);
    solver_k->pop();
    TRACE("ic3") << "model: " << G_model << std::endl;
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

  if (ctx().get_options().get_bool("ic3-use-weakening")) {
    assert(G_model.is_false(I1));
    // Try to waken I1
    I1 = weaken(I1, G_model, WEAK_FORWARD);
    TRACE("ic3") << "weakened I1: " << I1 << std::endl;
    assert(G_model.is_false(I1));
  }

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

  if (ctx().get_options().get_bool("ic3-use-weakening")) {
    assert(G_model.is_false(I2));
    // Try to weaken I2
    I2 = weaken(I2, G_model, WEAK_FORWARD);
    TRACE("ic3") << "weakened I2: " << I2 << std::endl;
    assert(G_model.is_false(I2));
  }

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
    d_counterexample.push_back(tm().mk_term(expr::TERM_NOT, f));
    return INDUCTION_FAIL;
  }

  // Learn something to refute G
  expr::term_ref learnt = learn_forward(d_induction_frame, G);
  TRACE("ic3") << "ic3: learnt: " << learnt << std::endl;

  // Add the learnt
  add_valid_up_to(d_induction_frame, learnt);

  // Try to push assumptions next time
  d_induction_obligations.push(induction_obligation(learnt, depth+1, 0));

  // Add to frame info
  assert(!d_frame_formula_info[learnt].invalid);
  d_frame_formula_info[learnt] = frame_formula_info(f, G);

  return INDUCTION_RETRY;
}

void ic3_engine::add_to_frame(size_t k, expr::term_ref f) {
  ensure_frame(k);
  assert(d_frame_content[k].count(f) == 0);
  get_solver(k)->add(f, smt::solver::CLASS_A);
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
    std::set<induction_obligation>::const_iterator it = d_induction_obligations_next.begin();
    for (; it != d_induction_obligations_next.end(); ++ it) {
      // Push if not shown invalid
      if (!d_frame_formula_info[it->formula()].invalid) {
        add_to_frame(d_induction_frame, it->formula());
        d_induction_obligations.push(*it);
      }
    }
    d_induction_obligations_next.clear();

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
  d_formula_scores.clear();
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
    d_counterexample.push_back(tm().mk_term(expr::TERM_NOT, P));
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
      reduce_learnts();
    }
  }

  return r;
}

const system::state_trace* ic3_engine::get_trace() {
  if (d_trace) { delete d_trace; }
  d_trace = new system::state_trace(d_transition_system->get_state_type());


  // Model we'll be using (the last one we're trying to extend)
  expr::model m(tm(), false);

  // Get the state variables
  const std::vector<expr::term_ref>& current_vars = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& next_vars = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);

  // Make the solver
  smt::solver* solver = smt::factory::mk_default_solver(tm(), ctx().get_options());
  solver->add_x_variables(current_vars.begin(), current_vars.end());
  solver->add_y_variables(next_vars.begin(), next_vars.end());
  solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);

  // Get the first one
  solver->push();
  solver->add(d_transition_system->get_initial_states(), smt::solver::CLASS_A);
  solver->add(d_counterexample[0], smt::solver::CLASS_A);
  smt::solver::result result = solver->check();
  unused_var(result);
  assert(result == smt::solver::SAT);
  solver->get_model(m);
  d_trace->add_model(m, system::state_type::STATE_CURRENT, 0);
  solver->pop();

  if (d_counterexample.size() > 1) {
    for (size_t k = 1; k < d_counterexample.size(); ++ k) {

      solver->push();

      // Add the model, i.e. where we're coming from
      for (size_t i = 0; i < next_vars.size(); ++ i) {
        expr::term_ref var = current_vars[i];
        expr::term_ref value = k == 1 ? m.get_variable_value(current_vars[i]) : m.get_variable_value(next_vars[i]);
        expr::term_ref eq = tm().mk_term(expr::TERM_EQ, var, value);
        solver->add(eq, smt::solver::CLASS_A);
      }

      // Add what we are trying to reach
      expr::term_ref to = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, d_counterexample[k]);
      d_trace->get_state_formula(to, k);
      solver->add(to, smt::solver::CLASS_B);

      // Check and add the model to the trace
      m.clear();
      smt::solver::result r = solver->check();
      assert(r == smt::solver::SAT);
      unused_var(r);
      solver->get_model(m);
      d_trace->add_model(m, system::state_type::STATE_NEXT, k);

      solver->pop();
    }
  }


  // Remove the solver
  delete solver;

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

void ic3_engine::bump_formula(expr::term_ref formula) {
  d_formula_scores[formula] ++;
}

void ic3_engine::bump_formulas(const std::vector<expr::term_ref>& formulas) {
  for (size_t i = 0; i < formulas.size(); ++ i) {
    bump_formula(formulas[i]);
  }
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

}
}
