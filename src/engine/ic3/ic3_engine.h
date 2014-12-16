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

namespace sal2 {
namespace ic3 {

/**
 * An obligation to do at frame k. This is just a carrier, the semantics
 * depend on the context. It could be that we're trying to satisfy P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
class obligation {
  size_t k;
  expr::term_ref P;
public:

  /** Construct the obligation */
  obligation(size_T k, expr::term_ref P)
  : k(k), P(P) {}

  /** Compare for equality */
  bool operator == (const obligation& o) const {
    return k == o.k && P = o.P;
  }

  /** Comparison for the queue, it's inverse because the queue pops the largest */
  bool operator < (const obligation& o) const {
    if (k == o.k) return P > o.P;
    return k > o.k;
  }
};

/** Priority queue for obligations */
typedef boost::heap::priority_queue<obligation> obligation_queue;


class ic3_engine : public engine {

  /** A solver per frame */
  std::vector<smt::solver*> d_solvers;

  /** Returns the solver for k-th frame */
  smt::solver* get_solver(size_t k);

  /** State variables */
  std::vector<expr::term_ref> d_state_variables;

  /** Next variables */
  std::vector<expr::term_ref> d_next_variables;

  /**
   * Checks the formula for satisfiablity in k-th frame, returns generalization
   * in k-th frame if satisfiable. F should be a formula in terms of state
   * variables (k-th frame) and optionally (k+1-th frame) variables. The generalization
   * will be in terms of current variables (k-th frame).
   */
  expr::term_ref check(size_t k, expr::term_ref F);

  /** Add a formula to k-th frame. */
  void add(size_t k, expr::term_ref F);

  /** Queue of induction obligations */
  obligation_queue d_induction_obligations;

  /** Add an induction obligation for frame k */
  void add_induction_obligation(size_t k, expr::term_ref f);

  /** Get the top induction obligation */


  /** Remove the top induction obligation */
  void pop_induction_obligation();

  /** Queue of safety obligations */
  obligation_queue d_satisfiablity_obligations;

  /** Add a satisfiablity obligation for frame k */
  void add_satisfiability_obligation(size_t k, expr::term_ref f);

  /** Pop the next satisfiability obligation */
  obligation pop_satisfiability_obligation() const;

public:

  ic3_engine(const system::context& ctx);
  ~ic3_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

};

}
}
