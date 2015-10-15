#include "reachability.h"

#include "system/state_type.h"
#include "utils/trace.h"

#include <vector>
#include <iostream>

namespace sally {
namespace ic3 {

reachability::reachability(const system::context& ctx)
: expr::gc_participant(ctx.tm())
, d_tm(ctx.tm())
, d_ctx(ctx)
, d_transition_system(0)
, d_smt(0)
{
  d_stats.reachable = new utils::stat_int("sally::ic3::reachable", 0);
  d_stats.unreachable = new utils::stat_int("sally::ic3::unreachable", 0);
  d_stats.queries = new utils::stat_int("sally::ic3::reachability_queries", 0);
  ctx.get_statistics().add(new utils::stat_delimiter());
  ctx.get_statistics().add(d_stats.reachable);
  ctx.get_statistics().add(d_stats.unreachable);
  ctx.get_statistics().add(d_stats.queries);
}

solvers::query_result reachability::check_one_step_reachable(size_t k, expr::term_ref F) {
  assert(k > 0);
  ensure_frame(k-1);

  d_stats.queries->get_value() ++;

  // The state type
  const system::state_type* state_type = d_transition_system->get_state_type();

  // Move the formula variables current -> next
  expr::term_ref F_next = state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F);

  // Query
  return d_smt->query_at(k-1, F_next, smt::solver::CLASS_B);
}


/** A reachability obligation at frame k. */
class reachability_obligation {

  /** The frame of the obligation */
  size_t d_k;
  /** The formula in question */
  expr::term_ref d_P;
  /** Local model of the formula */
  expr::model::ref d_P_model;

public:

  /** Construct the obligation */
  reachability_obligation(size_t k, expr::term_ref P, expr::model::ref P_model)
  : d_k(k), d_P(P), d_P_model(P_model)
  {}

  /** Get the frame */
  size_t frame() const { return d_k; }

  /** Get the formula */
  expr::term_ref formula() const { return d_P; }

  /** Get the model */
  expr::model::ref model() const { return d_P_model; }
};

reachability::status reachability::check_reachable(size_t start, size_t end, expr::term_ref f, expr::model::ref f_model, size_t& budget) {
  assert(budget > 0);
  assert(start == end);
  status result = UNREACHABLE;
  for (size_t k = start; k <= end; ++ k) {
    // Check reachability at k
    result = check_reachable(k, f, f_model, budget);
    // Check result of the current one
    switch (result) {
    case REACHABLE:
      return REACHABLE;
    case UNREACHABLE:
      break;
    case BUDGET_EXCEEDED:
      return BUDGET_EXCEEDED;
    }
    // Did we exceed the budget for the next call
    if (k < end && budget == 0) {
      return BUDGET_EXCEEDED;
    }
  }

  return UNREACHABLE;
}

reachability::status reachability::check_reachable(size_t k, expr::term_ref f, expr::model::ref f_model, size_t& budget) {

  TRACE("ic3") << "ic3: checking reachability at " << k << std::endl;

  assert(budget > 0);
  ensure_frame(k);

  // Queue of reachability obligations
  std::vector<reachability_obligation> reachability_obligations;
  reachability_obligations.push_back(reachability_obligation(k, f, f_model));

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
      // Remember the counterexample and notify the analyzer
      d_cex.clear();
      for (size_t i = 0; i < reachability_obligations.size(); ++ i) {
        d_cex.push_front(reachability_obligations[i].formula());
      }
      break;
    }

    // Check if the obligation is reachable
    solvers::query_result result = check_one_step_reachable(reach.frame(), reach.formula());
    if (result.result == smt::solver::UNSAT) {
      // Proven, remove from obligations
      reachability_obligations.pop_back();
      // Learn something at k that refutes the formula
      expr::term_ref learnt = d_smt->learn_forward(reach.frame(), reach.formula());
      // Add any unreachability learnts
      if (!frame_contains(reach.frame(), learnt)) {
        if (d_ctx.get_options().get_bool("ic3-add-backward")) {
          add_valid_up_to(reach.frame(), learnt);
        } else {
          add_to_frame(reach.frame(), learnt);
        }
      } else {
        // The only frame where we don't know consistency with formula
        assert(reach.frame() == k && reach.formula() == f);
      }
      // Use the budget unless we succeeded
      budget --;
      if (budget == 0 && !reachability_obligations.empty()) {
        return BUDGET_EXCEEDED;
      }
    } else {
      // New obligation to reach the counterexample
      reachability_obligations.push_back(reachability_obligation(reach.frame()-1, result.generalization, result.model));
    }
  }

  TRACE("ic3") << "ic3: " << (reachable ? "reachable" : "not reachable") << std::endl;

  // All discharged, so it's not reachable
  if (reachable) {
    d_stats.reachable->get_value() ++;
    return REACHABLE;
  } else {
    d_stats.unreachable->get_value() ++;
    return UNREACHABLE;
  }
}

void reachability::ensure_frame(size_t k) {
  // Upsize the frames if necessary
  while (d_frame_content.size() <= k) {
    // Add the empty frame content
    d_frame_content.push_back(formula_set());
    // Solvers new frame
    d_smt->new_reachability_frame();
  }
}

bool reachability::frame_contains(size_t k, expr::term_ref F) const {
  assert(k < d_frame_content.size());
  return d_frame_content[k].find(F) != d_frame_content[k].end();
}

void reachability::add_valid_up_to(size_t k, expr::term_ref F) {
  TRACE("ic3") << "ic3: adding at " << k << ": " << F << std::endl;
  ensure_frame(k);
  assert(k > 0);
  assert(k < d_frame_content.size());

  // Add to all frames from 1..k (not adding to 0, initial states need no refinement)
  int i;
  for(i = k; i >= 1; -- i) {
    if (frame_contains(i, F)) {
      break;
    }
    add_to_frame(i, F);
  }
  assert(i < (int) k);
}

void reachability::add_to_frame(size_t k, expr::term_ref f) {
  ensure_frame(k);
  assert(d_frame_content[k].find(f) == d_frame_content[k].end());

  // Add to solvers
  d_smt->add_to_reachability_solver(k, f);
  // Remember
  d_frame_content[k].insert(f);
}

const reachability::cex_type& reachability::get_cex() const {
  return d_cex;
}

void reachability::init(const system::transition_system* transition_system, solvers* smt_solvers) {
  d_transition_system = transition_system;
  d_smt = smt_solvers;
  d_cex.clear();
  d_frame_content.clear();
}

void reachability::clear() {
  d_transition_system = 0;
  d_smt = 0;
  d_cex.clear();
  d_frame_content.clear();
}

void reachability::gc_collect(const expr::gc_relocator& gc_reloc) {
  // TODO
}

}
}

