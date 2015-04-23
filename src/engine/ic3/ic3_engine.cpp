/*
 * ic3_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/ic3/ic3_engine.h"
#include "engine/ic3/solvers.h"

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
, d_trace(0)
, d_smt(0)
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

ic3_engine::~ic3_engine() {
  delete d_trace;
  delete d_smt;
}


void ic3_engine::reset() {

  d_transition_system = 0;
  d_property = 0;
  d_counterexample.clear();
  delete d_trace;
  d_trace = 0;
  d_induction_frame = 0;
  d_induction_obligations.clear();
  d_induction_obligations_next.clear();
  d_induction_obligations_count.clear();
  d_frame_content.clear();
  delete d_smt;
  d_smt = 0;
  for (size_t i = 0; i < d_stat_frame_size.size(); ++ i) {
    d_stat_frame_size[i]->get_value() = 0;
  }
}


expr::term_ref ic3_engine::check_one_step_reachable(size_t k, expr::term_ref F) {
  assert(k > 0);

  // The state type
  const system::state_type* state_type = d_transition_system->get_state_type();

  // Move the formula variables current -> next
  expr::term_ref F_next = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);

  // Query
  return d_smt->query_at(k-1, F_next, smt::solver::CLASS_B);
}

void ic3_engine::add_valid_up_to(size_t k, expr::term_ref F) {
  TRACE("ic3") << "ic3: adding at " << k << ": " << F << std::endl;
  assert(k > 0);
  assert(k < d_frame_content.size());

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

void ic3_engine::ensure_frame(size_t k) {

  MSG(1) << "ic3: Extending trace to " << k << std::endl;

  // Upsize the frames if necessary
  while (d_frame_content.size() <= k) {
    // Add the empty frame content
    d_frame_content.push_back(formula_set());
    // Number of obligations per frame
    d_induction_obligations_count.push_back(0);
    // Solvers new frame
    d_smt->new_frame();
  }
}

bool ic3_engine::frame_contains(size_t k, expr::term_ref f) {
  assert(k < d_frame_content.size());
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
        expr::term_ref learnt = d_smt->learn_forward(reach.frame(), reach.formula());
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

ic3_engine::induction_result ic3_engine::push_if_inductive(const induction_obligation& ind) {

  size_t depth = ind.depth();
  expr::term_ref f = ind.formula();

  assert(d_induction_frame < d_frame_content.size());
  assert(frame_contains(d_induction_frame, f));

  TRACE("ic3") << "ic3: pushing at " << d_induction_frame << ": " << f << std::endl;

  // Check if inductive
  expr::term_ref G = d_smt->check_inductive(f);

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
  expr::term_ref learnt = d_smt->learn_forward(d_induction_frame, G);
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
  assert(k < d_frame_content.size());
  assert(d_frame_content[k].count(f) == 0);

  // Add to solvers
  d_smt->add(k, f);

  // Remember
  d_frame_content[k].insert(f);
  if (k < d_stat_frame_size.size()) {
    d_stat_frame_size[k]->get_value() ++;
  }
}

void ic3_engine::extend_induction_failure(expr::term_ref f) {

  assert(d_counterexample.size() > 0);

  // We have a counter-example to inductiveness of f at at pushing frame
  // and d_counterexample has its generalization at the back.
  assert(d_counterexample.size() == d_induction_frame + 1);

  // Solver for checking
  smt::solver_scope solver_scope;
  d_smt->get_counterexample_solver(solver_scope);
  solver_scope.push();
  smt::solver* solver = solver_scope.get_solver();

  assert(d_smt->get_counterexample_solver_depth() == d_induction_frame);

  // Assert all the generalizations
  size_t k = 0;
  for (; k < d_counterexample.size(); ++ k) {
    // Add the generalization to frame k
    expr::term_ref G_k = d_trace->get_state_formula(d_counterexample[k], k);
    solver->add(G_k, smt::solver::CLASS_A);
  }

  // Try to extend it
  for (;; ++ k) {

    // We know there is a counterexample to induction of f: 0, ..., k-1, with f
    // being false at k. We try to extend it to falsify the reason we
    // introduced f. We introduced f to refute the counterexample to induction
    // of parent(f), which is witnessed by generalization refutes(f). We are
    // therefore looking to satisfy refutes(f) at k.
    assert(d_frame_formula_info[f].invalid == true);

    expr::term_ref G = d_frame_formula_info[f].refutes;
    expr::term_ref parent = d_frame_formula_info[f].parent;

    // If no more parents, we're done
    if (parent.is_null()) {
      break;
    }

    // Check at frame k
    d_smt->ensure_counterexample_solver_depth(k);
    solver->add(d_trace->get_state_formula(G, k), smt::solver::CLASS_A);

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

    // Move to the next frame (will also clear induction solver)
    d_induction_frame ++;
    d_induction_obligations.clear();
    ensure_frame(d_induction_frame);

    // Add formulas to the new frame
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
    d_smt->gc();

    // Restart if asked
    if (ctx().get_options().get_bool("ic3-enable-restarts")) {
      return engine::UNKNOWN;
    }
  }

  // Didn't prove or disprove, so unknown
  return engine::UNKNOWN;
}

engine::result ic3_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Initialize
  result r = UNKNOWN;
  d_induction_frame = 0;

  // Reset the engine
  reset();

  // Remember the input
  d_transition_system = ts;
  d_property = sf;

  // Make the trace
  if (d_trace) { delete d_trace; }
  d_trace = new system::state_trace(sf->get_state_type());

  // Initialize the solvers
  if (d_smt) { delete d_smt; }
  d_smt = new solvers(ctx(), ts, d_trace);

  // Start with at least one frame
  ensure_frame(0);

  // Add the initial state
  expr::term_ref I = d_transition_system->get_initial_states();
  add_to_frame(0, I);
  d_induction_obligations.push(induction_obligation(I, 0, 0));

  // Add the property we're trying to prove (if not already invalid at frame 0)
  expr::term_ref P = d_property->get_formula();
  expr::term_ref G = d_smt->query_at(0, tm().mk_term(expr::TERM_NOT, P), smt::solver::CLASS_A);
  if (G.is_null()) {
    add_to_frame(0, P);
    d_induction_obligations.push(induction_obligation(P, 0, 0));
  } else {
    return engine::INVALID;
  }

  while (r == UNKNOWN) {

    MSG(1) << "ic3: starting search" << std::endl;

    // Search
    r = search();
  }

  return r;
}

const system::state_trace* ic3_engine::get_trace() {

  // Add the property to the end of the counterexample
  d_counterexample.push_back(tm().mk_term(expr::TERM_NOT, d_property->get_formula()));
  d_trace->resize_to(d_counterexample.size());

  // Get the counterexample solver
  smt::solver_scope solver_scope;
  d_smt->get_counterexample_solver(solver_scope);
  smt::solver* solver = solver_scope.get_solver();
  solver_scope.push();

  // Assert needed stuff
  for (size_t k = 0; k < d_counterexample.size(); ++ k) {
    // Add the counter-example part
    expr::term_ref G = d_counterexample[k];
    expr::term_ref G_k = d_trace->get_state_formula(G, k);
    solver->add(G_k, smt::solver::CLASS_A);
  }

  // Add the unrolling
  d_smt->ensure_counterexample_solver_depth(d_counterexample.size()-1);
  d_smt->ensure_counterexample_solver_variables(d_counterexample.size()-1);

  // Check
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

void ic3_engine::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_counterexample);
  d_frame_formula_info.reloc(gc_reloc);
  assert(d_induction_obligations_next.size() == 0);
  for (size_t i = 0; i < d_frame_content.size(); ++ i) {
    gc_reloc.reloc(d_frame_content[i]);
  }
  d_smt->gc_collect(gc_reloc);
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

void ic3_engine::print_frames(std::ostream& out) const {
  for (size_t k = 0; k < d_frame_content.size(); ++ k) {
    print_frame(k, out);
  }
}

void ic3_engine::print_frame(size_t k, std::ostream& out) const {
  out << tm().mk_and(d_frame_content[k]) << std::endl;
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

std::ostream& operator << (std::ostream& out, const ic3_engine& ic3) {
  ic3.to_stream(out);
  return out;
}

}
}
