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
#include <iosfwd>

namespace sal2 {
namespace ic3 {

/**
 * An obligation to do at frame k. This is just a carrier, the semantics
 * depend on the context. It could be that we're trying to reach P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
class obligation {

  /** The frame of the obligation */
  size_t d_k;
  /** The forumula in question */
  expr::term_ref d_P;
  /** Assumption depth */
  size_t d_depth;

public:

  /** Construct the obligation */
  obligation(size_t k, expr::term_ref P, size_t depth)
  : d_k(k), d_P(P), d_depth(depth) {}

  /** Get the frame */
  size_t frame() const { return d_k; }

  /** Get the formula */
  expr::term_ref formula() const { return d_P; }

  /** Get the weight */
  size_t depth() const { return d_depth; }

  /** Compare for equality */
  bool operator == (const obligation& o) const {
    return d_k == o.d_k && d_P == o.d_P;
  }
};

/** Order on the induction obligations */
struct obligation_compare_induction {
  bool operator () (const obligation& o1, const obligation& o2) const;
};

/** Priority queue for obligations */
typedef boost::heap::priority_queue<obligation, boost::heap::compare<obligation_compare_induction> > induction_obligation_queue;

class ic3_engine : public engine {

  typedef std::set<expr::term_ref> formula_set;

  /** The transition system */
  const system::transition_system* d_transition_system;

  /** The property we're trying to prove */
  const system::state_formula* d_property;

  /** A solver per frame with next info */
  std::vector<smt::solver*> d_solvers;

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

  /** Push the formula forward if its inductive. Returns true if inductive. */
  bool push_if_inductive(size_t k, expr::term_ref f, size_t depth);

  /**
   * Add a formula that's inductive up to k-1 and holds at k. The formula will
   * be added to frames 0, ..., k, and additionally added to induction
   * obligations at k.
   */
  void add_inductive_at(size_t k, expr::term_ref f, size_t depth);

  /** Queue of induction obligations */
  induction_obligation_queue d_induction_obligations;

  /** Set of facts valid per frame */
  std::vector<formula_set> d_frame_content;

  /** Check if the frame contains the fiven formula */
  bool frame_contains(size_t k, expr::term_ref f);

  /** Make sure all frame content is ready */
  void ensure_frame(size_t k);

  /** Check if f is holds at k (added if holds) */
  bool check_valid_and_add(size_t k, expr::term_ref f, size_t depth);

  /** Check if f is reachable at k (nothing is added) */
  bool check_reachable(size_t k, expr::term_ref f);

  /** Solvers modified since last push */
  std::vector< std::set<size_t> > d_solvers_modified_per_push;

  /** Will push the solvers */
  void push_solvers();

  /** Pop the solvers modified since push */
  void pop_solvers();

  /** Are we in a push state */
  bool in_push() const;

  /** Print the frame content */
  void print_frame(size_t k, std::ostream& out) const;

  /** Print all frames */
  void print_frames(std::ostream& out) const;

  /** Generalize a SAT answer, but don't keep the known facts in the generalization */
  expr::term_ref generalize_sat_at(size_t k, smt::solver* solver);

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
