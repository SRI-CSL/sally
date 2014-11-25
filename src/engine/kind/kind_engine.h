/*
 * kind_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sal2 {
namespace kind {

/**
 * K-Induction engine.
 *
 * Prove:
 *
 * (1) P holds at 0, ..., k-1, i.e.
 *     I and T_0 and ... and T_{i-1} => P(x_i), for 0 <= i < k
 * (2) P holding at k consecutive step, implies it holds in the next one, i.e.
 *     and_{0 <= i < k} (P_i and T_i) => P_k
 */
class kind_engine : public engine {

  /** SMT solver for proving (1) */
  smt::solver* d_solver_1;

  /** SMT solver for proving (2) */
  smt::solver* d_solver_2;

  /** The type of the state variables */
  expr::term_ref d_state_type;

  /** Unrolling state variables */
  std::vector<expr::term_ref_strong> d_state_variables;

  /** Returns state variabels for state k */
  expr::term_ref state_variables(unsigned k, expr::term_ref type);

  /** Replace the variabels in f from 'from' to 'to' */
  expr::term_ref replace_vars(expr::term_ref f, expr::term_ref from, expr::term_ref to);

public:

  kind_engine(const system::context& ctx);
  ~kind_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

};

}
}
