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

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"
#include "expr/term_map.h"

#include "solvers.h"

#include <vector>
#include <boost/heap/priority_queue.hpp>
#include <boost/unordered_map.hpp>
#include <iosfwd>

namespace sally {
namespace ic3 {

class solvers;

/**
 * An obligation to do at frame k. This is just a carrier, the semantics
 * depend on the context. It could be that we're trying to reach P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
class induction_obligation {

  /** The formula in question */
  expr::term_ref d_P;
  /** Assumption depth */
  size_t d_depth;
  /** Any score */
  double d_score;

public:

  /** Construct the obligation */
  induction_obligation(expr::term_ref P, size_t depth, double score = 0)
  : d_P(P), d_depth(depth), d_score(score) {}

  /** Get the formula */
  expr::term_ref formula() const { return d_P; }

  /** Get the weight */
  size_t depth() const { return d_depth; }

  /** Get the score */
  double score() const { return d_score; }

  /** Add to score */
  void add_score(double amount) { d_score += amount; }

  /** Compare for equality */
  bool operator == (const induction_obligation& o) const {
    return d_P == o.d_P;
  }

  bool operator < (const induction_obligation& o) const {
    // Bigger depth wins
    if (depth() != o.depth()) {
      return depth() < o.depth();
    }
    // Smaller score wins
    if (score() != o.score()) {
      return score() > o.score();
    }
    // Break ties
    return formula() > o.formula();
  }

};

/** Priority queue for obligations */
typedef boost::heap::priority_queue<induction_obligation> induction_obligation_queue;

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
struct frame_formula_info {
  /** We introduced this formula to help inductivity of parent */
  expr::term_ref parent;
  /** This formula was introduced to eliminate this counter-example generalization */
  expr::term_ref refutes;
  /** Has this formula been shown refuted by a real conuterexample */
  bool invalid;

  frame_formula_info(): invalid(false) {}
  frame_formula_info(expr::term_ref parent, expr::term_ref refutes)
  : parent(parent), refutes(refutes), invalid(false) {}
};

class ic3_engine : public engine {

  typedef std::set<expr::term_ref> formula_set;

  /** The transition system */
  const system::transition_system* d_transition_system;

  /** The property we're trying to prove */
  const system::state_formula* d_property;

  /**
   * A counter-example, if any, to the current induction check. The queue is
   * stuffed with generalization, so the guarantee is that the every element
   * can reach the next element.
   */
  std::deque<expr::term_ref> d_counterexample;

  /** The trace we're building for counterexamples */
  system::state_trace* d_trace;

  /** The solvers */
  solvers* d_smt;

  /**
   * Checks if the formula is reachable in one step at frame k > 0. F should be
   * a formula in terms of state variables. The generalization will be in terms
   * of the state variables (k-1)-th frame.
   */
  solvers::query_result check_one_step_reachable(size_t k, expr::term_ref f);

  /**
   * Check if the formula or any of its parents is marked as invalid.
   */
  bool formula_or_parent_is_invalid(expr::term_ref f);

  enum induction_result {
    // Formula is inductive
    INDUCTION_SUCCESS,
    // Formula is not inductive with counter-example)
    INDUCTION_FAIL,
    // Formula is not directly inductive but the check decided to give up
    INDUCTION_INCONCLUSIVE,
    // Formula was not proven inductive, but new facts were added so we can try again
    INDUCTION_RETRY
  };

  /** Push the formula forward if its inductive. Returns true if inductive. */
  induction_result push_if_inductive(const induction_obligation& o);

  /**
   * Add a formula that's inductive up to k-1 and holds at k. The formula will
   * be added to frames 0, ..., k, and additionally added to induction
   * obligations at k.
   */
  void add_valid_up_to(size_t k, expr::term_ref f);

  /** The current frame we are trying to push */
  size_t d_induction_frame;

  /** Map from frame formulas to information about them */
  expr::term_ref_map<frame_formula_info> d_frame_formula_info;

  /** Mark the formula as invalid (not necessarily in the current frame) */
  void set_invalid(expr::term_ref f);

  /** Returns true if formula marked as invalid */
  bool is_invalid(expr::term_ref f) const;

  /** Returns true if formula of any of its parents are invalid */
  bool is_invalid_or_parent_invalid(expr::term_ref f) const;

  /** Queue of induction obligations at the current frame */
  induction_obligation_queue d_induction_obligations;

  /** Set of obligations for the next frame */
  std::vector<induction_obligation> d_induction_obligations_next;

  /** Count of obligations per frame */
  std::vector<size_t> d_induction_obligations_count;

  /** Get the next induction obligations */
  induction_obligation pop_induction_obligation();

  /** Set of facts valid per frame */
  std::vector<formula_set> d_frame_content;

  /** Returns the frame variable */
  expr::term_ref get_frame_variable(size_t i);

  /** Total number of facts in the database */
  size_t total_facts() const;

  /** Add the formula to frame */
  void add_to_frame(size_t k, expr::term_ref f);

  /** Add property to 0 frame, returns true if not immediately refuted */
  bool add_property(expr::term_ref P);

  /** Property components */
  std::set<expr::term_ref> d_properties;

  /** Is the property invalid */
  bool d_property_invalid;

  /** Check if the frame contains the fiven formula */
  bool frame_contains(size_t k, expr::term_ref f);

  /** Make sure all frame content is ready */
  void ensure_frame(size_t k);

  /**
   * Assuming f is satisfiable at k, check if f is reachable at k. During
   * exploration, new facts are added to frames, but no induction obligations.
   * After return the content of frame k-1 will be sufficient to prove
   * unreachability at k. Note that if k == 0, this returns true without any
   * checking.
   */
  bool check_reachable(size_t k, expr::term_ref f, expr::model::ref f_model);

  /** Print the frame content */
  void print_frame(size_t k, std::ostream& out) const;

  /** Print all frames */
  void print_frames(std::ostream& out) const;

  /** Statistics per frame (some number of frames) */
  std::vector<utils::stat_int*> d_stat_frame_size;

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

  /** Try to learn from the analyzer */
  void learn_from_analyzer(std::vector<expr::term_ref>& out);

public:

  ic3_engine(const system::context& ctx);
  ~ic3_engine();

  /** Query */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

  /** Output the state of the system to the stream */
  void to_stream(std::ostream& out) const;

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

}
}
