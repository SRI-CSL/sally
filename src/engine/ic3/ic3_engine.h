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

#include "solvers.h"
#include "reachability.h"

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"
#include "expr/term_map.h"

#include <vector>
#include <boost/heap/fibonacci_heap.hpp>
#include <boost/unordered_map.hpp>
#include <map>
#include <iosfwd>

namespace sally {
namespace ic3 {

class solvers;

/**
 * An obligation to do at frame k. This is just a carrier, the semantics
 * depend on the context. It could be that we're trying to reach P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
struct induction_obligation {

  /** The formula thar refutes the counter-example */
  expr::term_ref F_fwd;
  /** The counter-example generalization */
  expr::term_ref F_cex;
  /** Depth to the real counter-example */
  size_t d;
  /** Score of the obligation */
  double score;

  /** Construct the obligation */
  induction_obligation(expr::term_manager& tm, expr::term_ref F_fwd, expr::term_ref F_cex, size_t d, double score);

  /** Compare for equality */
  bool operator == (const induction_obligation& o) const;

  /** Compare the budget values */
  bool operator < (const induction_obligation& o) const;

  /** Bump the internal score (score is capped below at 1) */
  void bump_score(double amount);

};

std::ostream& operator << (std::ostream& out, const induction_obligation& ind);

/** Priority queue for obligations (max-heap) */
typedef boost::heap::fibonacci_heap<induction_obligation> induction_obligation_queue;

/**
 * Information on formulas. A formula is found in a frame because it refutes a
 * counterexample to induction of another formula. For all formulas F in a frame
 * we have that either
 *
 * * F has been there since the start, i.e. it is the property itself or
 *   the initial condition.
 * * We had a counter-example to induction G of some other F1 in the frame,
 *   and this counterexample is not reachable. From unreachability of G we
 *   learn another formula I, so we have that:
 *     - G => \exists x' T(x, x') and F1'
 *     - F => not G
 *
 * We keep the mapping from F to
 *   * parent: meaning F1 above
 *   * refutes: meaning G above
 *
 * THe parent links are non-circular and all end up in either F or some intial
 * state formula.
 */
struct frame_formula_parent_info {
  /** We introduced this formula to help inductivity of parent */
  expr::term_ref parent;
  /** This formula was introduced to eliminate this counter-example generalization */
  expr::term_ref refutes;
  /** How much depth > 0 */
  size_t depth;

  frame_formula_parent_info(): depth(0) {}
  frame_formula_parent_info(expr::term_ref parent, expr::term_ref refutes, size_t depth)
  : parent(parent), refutes(refutes), depth(depth) {}
};

class ic3_engine : public engine {

  typedef std::set<expr::term_ref> formula_set;

  /** The transition system */
  const system::transition_system* d_transition_system;

  /** The property we're trying to prove */
  const system::state_formula* d_property;

  /** The trace we're building for counterexamples */
  system::state_trace* d_trace;

  /** The solvers */
  solvers* d_smt;

  /** Reachability solver */
  reachability d_reachability;

  /** IC3 statistics */
  struct stats {
    utils::stat_int* frame_index;
    utils::stat_int* induction_depth;
    utils::stat_int* frame_size;
    utils::stat_int* frame_pushed;
    utils::stat_int* queue_size;
    utils::stat_int* max_cex_depth;
  } d_stats;


  /**
   * Checks if the formula is reachable in one step at frame k > 0. F should be
   * a formula in terms of state variables. The generalization will be in terms
   * of the state variables (k-1)-th frame.
   */
  solvers::query_result check_one_step_reachable(size_t k, expr::term_ref f);

  enum induction_result {
    // Formula is inductive
    INDUCTION_SUCCESS,
    // Formula is not inductive with counter-example
    INDUCTION_FAIL,
    // Formula was not proven inductive, but new facts were added so we can try again
    INDUCTION_RETRY
  };

  /** Push the formula forward if its inductive. Returns true if inductive. */
  induction_result push_obligation(induction_obligation& o);

  /** The current frame we are trying to push */
  size_t d_induction_frame_index;

  /** The current induction depth */
  size_t d_induction_frame_depth;

  /** Cutoff for the counter-examples */
  size_t d_induction_cutoff;

  /** The content of the induction frame */
  typedef std::set<induction_obligation> induction_frame_type;
  induction_frame_type d_induction_frame;

  /** Map from frame formulas to information about them */
  expr::term_ref_map<frame_formula_parent_info> d_frame_formula_parent_info;

  /** Sets the refutation info */
  void set_refutes_info(expr::term_ref f, expr::term_ref g, expr::term_ref l);

  /** Get the formula l refutes */
  expr::term_ref get_refutes(expr::term_ref l) const;

  /** Get the parent of l */
  expr::term_ref get_parent(expr::term_ref l) const;

  /** Get the depth of refutation */
  size_t get_refutes_depth(expr::term_ref l) const;

  /** Does l have a parent */
  bool has_parent(expr::term_ref l) const;

  /** Map from formulas to frame where its invalid */
  expr::term_ref_map<size_t> d_frame_formula_invalid_info;

  /** Mark the formula as invalid (not necessarily in the current frame) */
  void set_invalid(expr::term_ref f, size_t frame);

  /** Returns true if formula marked as invalid */
  bool is_invalid(expr::term_ref f) const;

  /** Queue of induction obligations at the current frame */
  induction_obligation_queue d_induction_obligations;

  /** Map from formulas to their positions in the queue */
  std::map<induction_obligation, induction_obligation_queue::handle_type> d_induction_obligations_handles;

  /** Set of obligations for the next frame */
  std::vector<induction_obligation> d_induction_obligations_next;

  /** Count of obligations per frame */
  std::vector<size_t> d_induction_obligations_count;

  /** Get the next induction obligations */
  induction_obligation pop_induction_obligation();

  /** Push to the obligation */
  void enqueue_induction_obligation(const induction_obligation& ind);

  /** Bump the score of the obligation */
  void bump_induction_obligation(const induction_obligation& ind, double amount);

  /** Returns the frame variable */
  expr::term_ref get_frame_variable(size_t i);

  /** Add property to 0 frame, returns true if not immediately refuted */
  bool add_property(expr::term_ref P);

  /** Add the initial states to 0 frame */
  void add_initial_states(expr::term_ref I, expr::term_ref P);

  /** Property components */
  std::set<expr::term_ref> d_properties;

  /** Is the property invalid */
  bool d_property_invalid;

  /**
   * The formula f has been shown not induction by a concrete counterexample.
   * The counterexample is recorded in C: d_counterexample. Try to extend it
   * forward by checking
   *
   *  C and G0 -> to refute p(C) at k + 1
   *  C and G0 and T and G1 -> to refute p(p(C)) at k + 2 ...
   *
   *  if G0 = p(C) by checking needed, since previous generalizations ensure
   *  that the extension is sat.
   */
  void extend_induction_failure(expr::term_ref f);

  /** Push the current frame */
  void push_current_frame();

  /** Search */
  result search();

  /** Reset the engine */
  void reset();

  /** GC the solvers */
  void gc_solvers();

  /** Types of learning */
  enum learning_type {
    LEARN_UNDEFINED,
    LEARN_FORWARD,
    LEARN_BACKWARD,
  };

  /** Type of learning to use */
  learning_type d_learning_type;

  /** Debug stuff */
  void dump_dependencies() const;

public:

  ic3_engine(const system::context& ctx);
  ~ic3_engine();

  /** Query */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

}
}
