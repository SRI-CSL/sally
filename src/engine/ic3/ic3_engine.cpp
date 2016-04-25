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

#include "engine/ic3/ic3_engine.h"
#include "engine/ic3/solvers.h"
#include "engine/factory.h"

#include "smt/factory.h"
#include "system/state_trace.h"
#include "utils/trace.h"
#include "expr/gc_relocator.h"

#include <stack>
#include <cassert>
#include <sstream>
#include <iostream>
#include <fstream>
#include <algorithm>

#define unused_var(x) { (void)x; }

namespace sally {
namespace ic3 {

// Fibonacci heap returns the top element in the order, so this should
bool induction_obligation_cmp::operator() (const induction_obligation& ind1, const induction_obligation& ind2) const {
  // Prefer deeper ones
  if (ind1.d != ind2.d) {
    return ind1.d > ind2.d;
  }
  // Prefer higher scores
  if (ind1.score != ind2.score) {
    return ind1.score < ind2.score;
  }
  // Otherwise just break ties, basically term id's => created earlier wins
  if (ind1.F_cex < ind2.F_cex) {
    return ind1.F_cex > ind2.F_cex;
  }
  return ind1.F_fwd > ind2.F_fwd;
}

induction_obligation::induction_obligation(expr::term_manager& tm, expr::term_ref F_fwd, expr::term_ref F_cex, size_t d, double score, size_t refined)
: F_fwd(F_fwd)
, F_cex(F_cex)
, d(d)
, score(score)
, refined(refined)
{}

bool induction_obligation::operator == (const induction_obligation& o) const {
  return F_cex == o.F_cex && F_fwd == o.F_fwd;
}

void induction_obligation::bump_score(double amount) {
  if (score + amount >= 0) {
    score += amount;
  } else {
    score = 0;
  }
}

bool induction_obligation::operator < (const induction_obligation& o) const {
  if (F_cex == o.F_cex) {
    return F_fwd < o.F_fwd;
  }
  return F_cex < o.F_cex;
}

std::ostream& operator << (std::ostream& out, const induction_obligation& ind) {
  out << ind.F_fwd;
  return out;
}

ic3_engine::ic3_engine(const system::context& ctx)
: engine(ctx)
, d_transition_system(0)
, d_property(0)
, d_trace(0)
, d_smt(0)
, d_reachability(ctx)
, d_induction_frame_index(0)
, d_induction_frame_depth(0)
, d_induction_frame_depth_count(0)
, d_induction_cutoff(0)
, d_induction_frame_next_index(0)
, d_property_invalid(false)
, d_learning_type(LEARN_UNDEFINED)
{
  d_stats.frame_index = new utils::stat_int("ic3::frame_index", 0);
  d_stats.induction_depth = new utils::stat_int("ic3::induction_depth", 0);
  d_stats.frame_size = new utils::stat_int("ic3::frame_size", 0);
  d_stats.frame_pushed = new utils::stat_int("ic3::frame_pushed", 0);
  d_stats.queue_size = new utils::stat_int("ic3::queue_size", 0);
  d_stats.max_cex_depth = new utils::stat_int("ic3::max_cex_depth", 0);
  ctx.get_statistics().add(new utils::stat_delimiter());
  ctx.get_statistics().add(d_stats.frame_index);
  ctx.get_statistics().add(d_stats.induction_depth);
  ctx.get_statistics().add(d_stats.frame_size);
  ctx.get_statistics().add(d_stats.frame_pushed);
  ctx.get_statistics().add(d_stats.queue_size);
  ctx.get_statistics().add(d_stats.max_cex_depth);
}

ic3_engine::~ic3_engine() {
  delete d_trace;
  delete d_smt;
}

void ic3_engine::reset() {

  d_transition_system = 0;
  d_property = 0;
  delete d_trace;
  d_trace = 0;
  d_induction_frame.clear();
  d_induction_frame_index = 0;
  d_induction_frame_depth = 0;
  d_induction_frame_depth_count = 0;
  d_induction_cutoff = 1;
  d_induction_obligations.clear();
  d_induction_obligations_next.clear();
  d_induction_obligations_count.clear();
  delete d_smt;
  d_smt = 0;
  d_properties.clear();
  d_property_invalid = false;
  d_reachability.clear();

  if (ai()) {
    ai()->clear();
  }
}

induction_obligation ic3_engine::pop_induction_obligation() {
  assert(d_induction_obligations.size() > 0);
  induction_obligation ind = d_induction_obligations.top();
  d_induction_obligations.pop();
  d_induction_obligations_handles.erase(ind);
  d_stats.queue_size->get_value() = d_induction_obligations.size();
  return ind;
}

void ic3_engine::enqueue_induction_obligation(const induction_obligation& ind) {
  assert(d_induction_frame.find(ind) != d_induction_frame.end());
  induction_obligation_queue::handle_type h = d_induction_obligations.push(ind);
  d_induction_obligations_handles[ind] = h;
  d_stats.queue_size->get_value() = d_induction_obligations.size();
}

ic3_engine::induction_result ic3_engine::push_obligation(induction_obligation& ind) {

  TRACE("ic3") << "ic3: Trying F_fwd at " << d_induction_frame_index << ": " << ind.F_fwd << std::endl;

  // Check if F_cex is inductive. If not then, if it can be reached, we can find a counter-example.
  solvers::query_result fwd_result = d_smt->check_inductive(ind.F_fwd);

  // If UNSAT we can push it
  if (fwd_result.result == smt::solver::UNSAT) {    
    // It's pushed so add it to induction assumptions
    assert(d_induction_frame.find(ind) != d_induction_frame.end());
    TRACE("ic3") << "ic3: pushed " << ind.F_fwd << std::endl;
    // Add it to set of pushed facts
    d_induction_obligations_next.push_back(ind);
    d_stats.frame_pushed->get_value() = d_induction_obligations_next.size();
    // We're done
    return INDUCTION_SUCCESS;
  }

  // If more than cutoff, just break
  if (ind.d >= d_induction_cutoff) {
    return INDUCTION_FAIL;
  }

  expr::term_ref F_fwd_not = tm().mk_term(expr::TERM_NOT, ind.F_fwd);
  expr::term_ref F_cex_not = tm().mk_term(expr::TERM_NOT, ind.F_cex);

  // We have a model for
  //
  //   F F ..... F !F
  //
  // If the model satisfies CEX in the last state, we try to extend the
  // counter-example, otherwise, we fail the push.
  solvers::query_result cex_result = d_smt->check_inductive_model(fwd_result.model, ind.F_cex);
  if (cex_result.result == smt::solver::UNSAT) {
    cex_result = d_smt->check_inductive(F_cex_not);
  }
  if (cex_result.result == smt::solver::SAT) {
    // We can actually reach the counterexample of induction from G, so we check if
    // it's reachable.
    TRACE("ic3") << "ic3: F_cex generalization " << cex_result.generalization << std::endl;

    // Check if G is reachable. We know that F_cex is not reachable up to induction frame index.
    // This means that G can be reached at index i, then F_cex is reachable at i + induction_depth.
    // Therefore i + induction_depth > frame_index, hence we check from i = frame_index - depth + 1 to frame_index
    size_t start = (d_induction_frame_index + 1) - d_induction_frame_depth;
    size_t end = d_induction_frame_index;
    reachability::status reachable = d_reachability.check_reachable(start, end, cex_result.generalization, cex_result.model);

    // If reachable, then G leads to F_cex, and F_cex leads to !P
    if (reachable.r == reachability::REACHABLE) {
      d_property_invalid = true;
      return INDUCTION_FAIL;
    }

    // G is not reachable, so !G holds up to current frame index
    expr::term_ref F_cex = cex_result.generalization;
    TRACE("ic3") << "ic3: new F_cex: " << F_cex << std::endl;

    // Learn something forward that refutes G
    // We know that G_not is not satisfiable
    expr::term_ref F_fwd = d_smt->learn_forward(d_induction_frame_index, F_cex);
    TRACE("ic3") << "ic3: new F_fwd: " << F_fwd << std::endl;

    // Add to counter-example to induction frame
    induction_obligation new_ind(tm(), F_fwd, F_cex, d_induction_frame_depth + ind.d, 1);
    assert(d_induction_frame.find(new_ind) == d_induction_frame.end());
    d_induction_frame.insert(new_ind);
    d_stats.frame_size->get_value() = d_induction_frame.size();
    d_smt->add_to_induction_solver(F_fwd, solvers::INDUCTION_FIRST);
    d_smt->add_to_induction_solver(F_fwd, solvers::INDUCTION_INTERMEDIATE);
    enqueue_induction_obligation(new_ind);

    // We have to learn :(, decrease the score, let others go for a change
    ind.score *= 0.99;

    // Now, retry
    return INDUCTION_RETRY;
  }

  // So we have a model of !F_fwf && !F_cex
  solvers::query_result cti_result = d_smt->check_inductive_model(fwd_result.model, F_fwd_not);
  assert(cti_result.result == smt::solver::SAT);

  // Check if it's reachable
  size_t start = (d_induction_frame_index + 1) - d_induction_frame_depth;
  size_t end = d_induction_frame_index;
  reachability::status reachable = d_reachability.check_reachable(start, end, cti_result.generalization, cti_result.model);

  if (reachable.r == reachability::REACHABLE) {
    // Current obligation is false at reach + depth. So we can move to at most
    // reach + k next time;
    //
    // This particular CTI is reachable in k + depth. There might be others that
    // are shorter than this.

    // Find out the smallest index where F_fwd is falsified
    start = d_induction_frame_index + 1;
    end = std::min(reachable.k + d_induction_frame_depth, d_induction_frame_next_index);
    if (start < end) {
      reachable = d_reachability.check_reachable(start, end, F_fwd_not, expr::model::ref());
      if (reachable.r == reachability::REACHABLE) {
        // We have to adapt the next index
        d_induction_frame_next_index = reachable.k;
      }
    } else {
      d_induction_frame_next_index = end;
    }

    // We know that CEX is not reachable (FULL CHECK ABOVE), otherwise we wouldn't be here.
    // Therefore !CEX is k-inductive modulo current assumptions and we can just push it
    induction_obligation new_ind(tm(), F_cex_not, ind.F_cex, ind.d, ind.score);
    assert(d_induction_frame.find(new_ind) == d_induction_frame.end());
    d_induction_frame.insert(new_ind);
    d_stats.frame_size->get_value() = d_induction_frame.size();
    // No need to assert anything, we already have F_fwd => !F_cex
    // Also, just add to next
    d_induction_obligations_next.push_back(new_ind);
    d_stats.frame_pushed->get_value() = d_induction_obligations_next.size();

    // Current obligation has failed, we know it will become invalid
    return INDUCTION_FAIL;
  }

  // Learn something forward that refutes reachability of CTI
  expr::term_ref F_fwd = d_smt->learn_forward(d_induction_frame_index, cti_result.generalization);
  d_smt->add_to_induction_solver(F_fwd, solvers::INDUCTION_FIRST);
  d_smt->add_to_induction_solver(F_fwd, solvers::INDUCTION_INTERMEDIATE);

  F_fwd = tm().mk_and(ind.F_fwd, F_fwd);
  TRACE("ic3") << "ic3: new F_fwd: " << F_fwd << std::endl;

  // We know what F_fwd removes the CTI, and F_fwd => !CEX, so we can add it
  d_induction_frame.erase(ind);
  ind = induction_obligation(tm(), F_fwd, ind.F_cex, ind.d, ind.score*0.99, ind.refined + 1);
  d_induction_frame.insert(ind);

  // Current obligation has failed, but we replaced it
  return INDUCTION_RETRY;
}

void ic3_engine::push_current_frame() {

  // Search while we have something to do
  while (!d_induction_obligations.empty() && !d_property_invalid) {

    // Pick a formula to try and prove inductive, i.e. that F_k & P & T => P'
    induction_obligation ind = pop_induction_obligation();

    // Push the formula forward if it's inductive at the frame
    induction_result ind_result = push_obligation(ind);

    // See what happened
    switch (ind_result) {
    case INDUCTION_RETRY:
      // We'll retry the same formula (it's already added to the solver)
      enqueue_induction_obligation(ind);
      break;
    case INDUCTION_SUCCESS:
      // Boss, we're done with this one
      break;
    case INDUCTION_FAIL:
      // Failure, we didn't push, either counter-example found, or we couldn't push
      // and decided not to try again
      break;
    }
  }
}

engine::result ic3_engine::search() {

  // Push frame by frame */
  for(;;) {

    // Set the cutoff
    d_induction_cutoff = std::numeric_limits<size_t>::max();
    // d_induction_cutoff = d_induction_frame_index + d_induction_frame_depth;

    // Set how far we can go
    // d_induction_frame_next_index = d_induction_frame_index + 1;
    d_induction_frame_next_index = d_induction_frame_index + d_induction_frame_depth;

    MSG(1) << "ic3: working on induction frame " << d_induction_frame_index << " (" << d_induction_frame.size() << ") with induction depth " << d_induction_frame_depth << " and cutoff " << d_induction_cutoff << std::endl;

    // Push the current induction frame forward
    size_t previous_frame_size = d_induction_frame.size();
    push_current_frame();

    // If we've disproved the property, we're done
    if (d_property_invalid) {
      return engine::INVALID;
    }

    MSG(1) << "ic3: pushed " << d_induction_obligations_next.size() << " of " << d_induction_frame.size() << std::endl;

    // If we pushed everything, we're done
    if (d_induction_frame.size() == d_induction_obligations_next.size()) {
      if (ctx().get_options().get_bool("ic3-show-invariant")) {
        d_smt->print_formulas(d_induction_frame, std::cout);
      }
      return engine::VALID;
    }

    // Set depth of induction for next time
    if (previous_frame_size < d_induction_frame.size()) {
      d_induction_frame_depth = d_induction_frame_next_index + 1;
    }

    // Clear induction obligations queue and the frame
    d_induction_obligations.clear();
    d_induction_frame.clear();
    d_stats.frame_size->get_value() = 0;

    // If exceeded number of frames
    if (ctx().get_options().get_unsigned("ic3-max") > 0 && d_induction_frame_index >= ctx().get_options().get_unsigned("ic3-max")) {
      return engine::INTERRUPTED;
    }

    // Next frame position
    d_induction_frame_index = d_induction_frame_next_index;

    if (ctx().get_options().get_unsigned("ic3-induction-max") != 0 && d_induction_frame_depth > ctx().get_options().get_unsigned("ic3-induction-max")) {
      d_induction_frame_depth = ctx().get_options().get_unsigned("ic3-induction-max");
    }
    d_smt->reset_induction_solver(d_induction_frame_depth);

    // Add formulas to the new frame
    d_induction_frame.clear();
    std::vector<induction_obligation>::const_iterator next_it = d_induction_obligations_next.begin();
    for (; next_it != d_induction_obligations_next.end(); ++ next_it) {
      // The formula
      induction_obligation ind = *next_it;
      ind.score = ind.score/2 + 1; // Keep old score and add 1 for effort
      assert(d_induction_frame.find(ind) == d_induction_frame.end());
      d_smt->add_to_induction_solver(ind.F_fwd, solvers::INDUCTION_FIRST);
      d_smt->add_to_induction_solver(ind.F_fwd, solvers::INDUCTION_INTERMEDIATE);
      d_induction_frame.insert(ind);
      d_stats.frame_size->get_value() = d_induction_frame.size();
      enqueue_induction_obligation(ind);
    }

    // Clear next frame info
    d_induction_obligations_next.clear();
    d_stats.frame_pushed->get_value() = 0;

    // Update stats
    d_stats.frame_index->get_value() = d_induction_frame_index;
    d_stats.induction_depth->get_value() = d_induction_frame_depth;

    // Do garbage collection
    d_smt->gc();
  }

  // Didn't prove or disprove, so unknown
  return engine::UNKNOWN;
}

engine::result ic3_engine::query(const system::transition_system* ts, const system::state_formula* sf) {

  // Initialize
  result r = UNKNOWN;

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

  // Initialize the reachability solver
  d_reachability.init(d_transition_system, d_smt);

  // Initialize the induction solver
  d_induction_frame_index = 0;
  d_induction_frame_depth = 1;
  d_induction_cutoff = 1;
  d_smt->reset_induction_solver(1);

  // Add the property we're trying to prove (if not already invalid at frame 0)
  bool ok = add_property(d_property->get_formula());
  if (!ok) {
    return engine::INVALID;
  }

  while (r == UNKNOWN) {

    MSG(1) << "ic3: starting search" << std::endl;

    // Search
    r = search();
  }

  MSG(1) << "ic3: search done: " << r << std::endl;

  return r;
}

bool ic3_engine::add_property(expr::term_ref P) {
  smt::solver::result result = d_smt->query_at_init(tm().mk_term(expr::TERM_NOT, P));
  if (result == smt::solver::UNSAT) {
    induction_obligation ind(tm(), P, tm().mk_term(expr::TERM_NOT, P), /* cex depth */ 0, /* score */ 1);
    if (d_induction_frame.find(ind) == d_induction_frame.end()) {
      // Add to induction frame, we know it holds at 0
      assert(d_induction_frame_depth == 1);
      d_induction_frame.insert(ind);
      d_stats.frame_size->get_value() = d_induction_frame.size();
      d_smt->add_to_induction_solver(P, solvers::INDUCTION_FIRST);
      enqueue_induction_obligation(ind);
    }
    d_properties.insert(P);
    return true;
  } else {
    return false;
  }
}

const system::state_trace* ic3_engine::get_trace() {
  return d_trace;
}

void ic3_engine::gc_collect(const expr::gc_relocator& gc_reloc) {
  assert(d_induction_obligations_next.size() == 0);
  d_smt->gc_collect(gc_reloc);
  d_reachability.gc_collect(gc_reloc);
}


}
}
