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
 * depend on the context. It could be that we're trying to satisfy P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
class obligation {
  size_t d_k;
  expr::term_ref d_P;
  int d_weight;
public:

  /** Construct the obligation */
  obligation(size_t k, expr::term_ref P, int weight)
  : d_k(k), d_P(P), d_weight(weight) {}

  /** Get the frame */
  size_t frame() const {
    return d_k;
  }

  /** Get the formula */
  expr::term_ref formula() const {
    return d_P;
  }

  int weight() const {
    return d_weight;
  }

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

  /** A solver per frame */
  std::vector<smt::solver*> d_solvers;

  /** Returns the solver for k-th frame */
  smt::solver* get_solver(size_t k);

  /**
   * Checks if the formula is reachable in one step at frame k > 0. F should be
   * a formula in terms of state variables. The generalization will be in terms
   * of the state variables (k-1)-th frame.
   */
  expr::term_ref check_one_step_reachable(size_t k, expr::term_ref F);

  /**
   * Checks if the formula is inductive in k-th frame, returns counterexample
   * generalization in k-th frame if not. F should be a formula in terms of state
   * variables (k-th frame). The generalization will be in terms of current
   * variables (k-th frame).
   */
  expr::term_ref check_inductive_at(size_t k, expr::term_ref F);

  /**
   * Add a newly learnt formula. The formula will be added to
   * frames 0, ..., k, and additionally added to induction obligations.
   */
  void add_learnt(size_t k, expr::term_ref F, int weight);

  /** Queue of induction obligations */
  induction_obligation_queue d_induction_obligations;

  /** Set of facts valid per frame */
  std::vector<formula_set> d_frame_content;

  /** Check if the frame contains the fiven formula */
  bool frame_contains(size_t k, expr::term_ref f);

  /** Make sure all frame content is ready */
  void ensure_frame(size_t k);

  /** Max number of frames */
  unsigned d_max_frames;

  /** Max number of facts */
  unsigned d_max_frame_size;

  /** Check if f is holds at k (added if holds) */
  bool check_valid_and_add(size_t k, expr::term_ref f, int weight);

  /** Check if f is reachable at k (negation added if not reachable) */
  bool check_reachable_and_add(size_t k, expr::term_ref f, int weight);

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
