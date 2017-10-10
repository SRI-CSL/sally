/*
 * reachability.h
 *
 *  Created on: Oct 13, 2015
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "expr/model.h"
#include "system/context.h"
#include "system/transition_system.h"
#include "solvers.h"
#include "cex_manager.h"

#include <deque>

namespace sally {
namespace pdkind {

class reachability : public expr::gc_participant {

public:

  /** Status of reachability checks */
  enum result {
    REACHABLE,
    UNREACHABLE
  };

  struct status {
    // The result
    result r;
    // The frame where reachable, if any
    size_t k;
  };


private:

  /** The term manager */
  const expr::term_manager& d_tm;

  /** The context */
  const system::context& d_ctx;

  /** The transition system */
  const system::transition_system* d_transition_system;

  /** Solvers we're using */
  solvers* d_smt;

  /** CEX manager */
  cex_manager& d_cex_manager;

  struct stats {
    /** Number of reachability SMT queries */
    utils::stat_int* queries;
    /** Number of reachable results */
    utils::stat_int* reachable;
    /** Number of unreachable reasults */
    utils::stat_int* unreachable;

  } d_stats;

  typedef std::set<expr::term_ref> formula_set;

  /** Set of facts valid per frame */
  std::vector<formula_set> d_frame_content;

  /** Ensure that frame k is setup properly */
  void ensure_frame(size_t k);

  /** Check if frame contains F */
  bool frame_contains(size_t k, expr::term_ref f) const;

  /**
   * Check if F is reachable in one step from at frame k.
   */
  solvers::query_result check_one_step_reachable(size_t k, expr::term_ref F);

  /**
   * Check if f is reachable at k, assuming f is unreachable in < k steps.
   */
  result check_reachable(size_t k, expr::term_ref f, size_t property_id);

public:

  /** Construct the reachability checker */
  reachability(const system::context& ctx, cex_manager& cm);

  /** Initialize the reachability engine */
  void init(const system::transition_system* transition_system, solvers* smt_solvers);

  /** Clear all internal data */
  void clear();

  /**
   * Add to frame k.
   */
  void add_to_frame(size_t k, expr::term_ref F);

  /**
   * Add to frames 1..k.
   */
  void add_valid_up_to(size_t k, expr::term_ref F);

  /**
   * Check if f is reachable at any frame start, ..., end, assuming f is unreachable
   * in < start steps.
   *
   * It returns unreachable, one can use learn_froward to learn something true
   * 0 ... end, that refutes f.
   *
   * If it returns reachable, the counter-example generalizations are stored in
   * d_cex (of lenght start <= l <= end) and can be obtained with get_cex().
   */
  status check_reachable(size_t start, size_t end, expr::term_ref f, size_t property_id);

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

}
}
