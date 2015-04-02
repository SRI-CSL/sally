/*
 * ic3_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>
#include <boost/heap/priority_queue.hpp>
#include <boost/unordered_map.hpp>
#include <iosfwd>

namespace sally {
namespace ic3 {

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
    // Smaller depth wins
    if (depth() != o.depth()) {
      return depth() > o.depth();
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

  /** A solver per frame with next info */
  std::vector<smt::solver*> d_solvers;

  /** A counter-example, if any, with formulas in reverse order, i.e. last one is the 0 frame */
  std::deque<expr::term_ref> d_counterexample;

  /** The trace we're building for counterexamples */
  system::state_trace* d_trace;

  /** Returns the solver for k-th frame */
  smt::solver* get_solver(size_t k);

  /**
   * Checks if the formula is reachable in one step at frame k > 0. F should be
   * a formula in terms of state variables. The generalization will be in terms
   * of the state variables (k-1)-th frame.
   */
  expr::term_ref check_one_step_reachable(size_t k, expr::term_ref f);

  /**
   * Checks if the formula is inductive in k-th frame, returns counterexample
   * generalization in k-th frame if not. F should be a formula in terms of state
   * variables (k-th frame). The generalization will be in terms of current
   * variables (k-th frame).
   */
  expr::term_ref check_inductive_at(size_t k, expr::term_ref f);

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
  std::map<expr::term_ref, frame_formula_info> d_frame_formula_info;

  /** Queue of induction obligations at the current frame */
  induction_obligation_queue d_induction_obligations;

  /** Set of obligations for the next frame */
  std::set<induction_obligation> d_induction_obligations_next;

  /** Count of obligations per frame */
  std::vector<size_t> d_induction_obligations_count;

  /** Get the next induction obligations */
  induction_obligation pop_induction_obligation();

  /** Set of facts valid per frame */
  std::vector<formula_set> d_frame_content;

  /** Total number of facts in the database */
  size_t total_facts() const;

  /** set of facts that are inductive at frame */
  std::vector<formula_set> d_frame_inductive_content;

  /** Add the formul to frame */
  void add_to_frame(size_t k, expr::term_ref f);

  /** Check if the frame contains the fiven formula */
  bool frame_contains(size_t k, expr::term_ref f);

  /** Create and initialize the solver k */
  void init_solver(size_t k);

  /** Make sure all frame content is ready */
  void ensure_frame(size_t k);

  /** Remove some learnt formulas */
  void reduce_learnts();

  /**
   * Check if f is holds at frame k. */
  bool check_valid(size_t k, expr::term_ref f);

  /**
   * Assuming f is satisfiable at k, check if f is reachable at k. During
   * exploration, new facts are added to frames, but no induction obligations.
   * After return the content of frame k-1 will be sufficient to prove
   * unreachability at k. Note that if k == 0, this returns true without any
   * checking.
   */
  bool check_reachable(size_t k, expr::term_ref f);

  /** Print the frame content */
  void print_frame(size_t k, std::ostream& out) const;

  /** Print all frames */
  void print_frames(std::ostream& out) const;

  /** Generalize a SAT answer, but don't keep the known facts in the generalization */
  expr::term_ref generalize_sat_at(size_t k, smt::solver* solver);

  /** Given G unsat at 0, ..., k, return something at valid 0...k that refutes G. */
  expr::term_ref learn_forward(size_t k, expr::term_ref G);

  /** Replace any x = y in G with (x <= y) & (x >= y) */
  expr::term_ref eq_to_ineq(expr::term_ref G);

  enum weakening_mode {
    // F => W(F), with F false and W(F) false
    WEAK_FORWARD,
    // W(F) => F, with F true, and W(F) true
    WEAK_BACKWARD
  };

  /**
   * Weaken the given formula, i.e. find W such that F => W and and W is
   * inconsistnet with the given model.
   */
  expr::term_ref weaken(expr::term_ref F, expr::model& m, weakening_mode mode);

  /** Statistics per frame (some number of frames) */
  std::vector<utils::stat_int*> d_stat_frame_size;

  /** Push the current frame */
  void push_current_frame();

  /** Search */
  result search();

  /** Check if all frames are satisfiable, throw otherwise */
  void check_deadlock();

  typedef boost::unordered_map<expr::term_ref, size_t, expr::term_ref_hasher> formula_scores_map;

  /** Map from formulas to their scores (how many times they were used as assumptions) */
  formula_scores_map d_formula_scores;

  /** Returns the score of the formula (or 0 if it doesn't have one) */
  size_t get_score(expr::term_ref f) const;

  /** Comparator for scores */
  struct learnt_cmp {
    const formula_scores_map& scores;
    bool operator () (expr::term_ref f1, expr::term_ref f2) const;
    learnt_cmp(const formula_scores_map& scores): scores(scores) {}
  };

  /** Bump the scores of the formula */
  void bump_formula(expr::term_ref formulas);

  /** Bump the scores of the formulas */
  void bump_formulas(const std::vector<expr::term_ref>& formulas);

  /** Reset the engine */
  void reset();

public:

  ic3_engine(const system::context& ctx);
  ~ic3_engine();

  /** Query */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

  /** Output the state of the system to the stream */
  void to_stream(std::ostream& out) const;

};

}
}
