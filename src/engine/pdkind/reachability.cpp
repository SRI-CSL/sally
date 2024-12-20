#include "reachability.h"

#include "system/state_type.h"
#include "utils/trace.h"

#include <vector>
#include <iostream>

namespace sally {
namespace pdkind {

reachability::reachability(const system::context& ctx, cex_manager& cm)
: expr::gc_participant(ctx.tm())
, d_tm(ctx.tm())
, d_ctx(ctx)
, d_transition_system(0)
, d_smt(0)
, d_cex_manager(cm)
{
  d_stats.reachable = new utils::stat_int("sally::pdkind::reachable", 0);
  d_stats.unreachable = new utils::stat_int("sally::pdkind::unreachable", 0);
  d_stats.queries = new utils::stat_int("sally::pdkind::reachability_queries", 0);
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
  return d_smt->query_with_transition_at(k-1, F_next, smt::solver::CLASS_B);
}


/** A reachability obligation at frame k. */
class reachability_obligation {

  /** The frame of the obligation */
  size_t d_k;
  /** The formula in question */
  expr::term_ref d_P;

public:

  /** Construct the obligation */
  reachability_obligation(size_t k, expr::term_ref P)
  : d_k(k), d_P(P)
  {}

  /** Get the frame */
  size_t frame() const { return d_k; }

  /** Get the formula */
  expr::term_ref formula() const { return d_P; }

};

reachability::status reachability::check_reachable(size_t start, size_t end, expr::term_ref f, size_t property_id) {
  assert(start <= end);

  status result;

  for (result.k = start; result.k <= end; ++ result.k) {
    // Check reachability at k
    result.r = check_reachable(result.k, f, property_id);
    // Check result of the current one
    if (result.r == REACHABLE) {
      break;
    }
  }

  return result;
}

reachability::result reachability::check_reachable(size_t k, expr::term_ref f, size_t property_id) {

  TRACE("pdkind") << "pdkind: checking reachability at " << k << std::endl;

  ensure_frame(k);

  // Special case for k = 0
  if (k == 0) {
    smt::solver::result result = d_smt->query_at_init(f);
    switch (result) {
    case smt::solver::UNSAT:
      TRACE("pdkind") << "pdkind: checking reachability at " << k << ": unreachable" << std::endl;
      return UNREACHABLE;
    case smt::solver::SAT:
      TRACE("pdkind") << "pdkind: checking reachability at " << k << ": reachable" << std::endl;
      if (property_id != d_cex_manager.null_property_id) {
        d_cex_manager.mark_root(f, property_id);
      }
      return REACHABLE;
    default:
      assert(false);
    }
  }

  // Queue of reachability obligations
  std::vector<reachability_obligation> reachability_obligations;
  reachability_obligations.push_back(reachability_obligation(k, f));

  // We're not reachable, if we hit 0 we set it to true
  bool reachable = false;

  // The induction not valid, try to extend to full counter-example
  while (!reachability_obligations.empty()) {
    // Get the next reachability obligations
    reachability_obligation reach = reachability_obligations.back();
    // If we're at 0 frame, we're reachable: anything passed in is consistent
    // part of the abstraction
    if (reach.frame() == 0) {
      // We're reachable since we got here by going back to I, mark it
      reachable = true;
      // Remember the counterexample
      if (property_id != d_cex_manager.null_property_id) {
        d_cex_manager.mark_root(reach.formula(), property_id);
        for (size_t i = 0; i + 1 < reachability_obligations.size(); ++ i) {
          // Adding in reverse order
          expr::term_ref B = reachability_obligations[i].formula();
          expr::term_ref A = reachability_obligations[i+1].formula();
          d_cex_manager.add_edge(A, B, 1, property_id);
        }
      }
      // Done
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
        if (d_ctx.get_options().get_bool("pdkind-add-backward")) {
          add_valid_up_to(reach.frame(), learnt);
        } else {
          add_to_frame(reach.frame(), learnt);
        }
      } else {
        // The only frame where we don't know consistency with formula
        assert(reach.frame() == k && reach.formula() == f);
      }
    } else {
      // New obligation to reach the counterexample
      reachability_obligations.push_back(reachability_obligation(reach.frame()-1, result.generalization));
    }
  }

  TRACE("pdkind") << "pdkind: " << (reachable ? "reachable" : "not reachable") << std::endl;

  // All discharged, so it's not reachable
  if (reachable) {
    TRACE("pdkind") << "pdkind: checking reachability at " << k << ": reachable" << std::endl;
    d_stats.reachable->get_value() ++;
    return REACHABLE;
  } else {
    TRACE("pdkind") << "pdkind: checking reachability at " << k << ": unreachable" << std::endl;
    d_stats.unreachable->get_value() ++;
    return UNREACHABLE;
  }
}

void reachability::ensure_frame(size_t k) {
  // Upsize the frames if necessary
  while (d_frame_content.size() <= k) {
    // Add the empty frame content
    d_frame_content.push_back(formula_set());
    d_smt->new_reachability_frame();
  }
}

bool reachability::frame_contains(size_t k, expr::term_ref F) const {
  assert(k < d_frame_content.size());
  return d_frame_content[k].find(F) != d_frame_content[k].end();
}

void reachability::add_valid_up_to(size_t k, expr::term_ref F) {
  TRACE("pdkind") << "pdkind: adding at " << k << ": " << F << std::endl;
  ensure_frame(k);
  assert(k > 0);

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

void reachability::init(const system::transition_system* transition_system, solvers* smt_solvers) {
  d_transition_system = transition_system;
  d_smt = smt_solvers;
  d_frame_content.clear();
}

void reachability::clear() {
  d_transition_system = 0;
  d_smt = 0;
  d_frame_content.clear();
}

void reachability::gc_collect(const expr::gc_relocator& gc_reloc) {
  // TODO
}

}
}

