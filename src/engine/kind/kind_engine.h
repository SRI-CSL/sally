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

#include <vector>

namespace sally {
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
 *
 * Options kind-min and kind-max set the range of k to try.
 */
class kind_engine : public engine {

  /** SMT solver for proving (1) */
  smt::solver* d_solver_1;

  /** SMT solver for proving (2) */
  smt::solver* d_solver_2;

  /** The trace we're building */
  system::state_trace* d_trace;

  /** The invariant if proven */
  expr::term_ref d_invariant;

public:

  kind_engine(const system::context& ctx);
  ~kind_engine();

  /** Query */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

  /** Invariant (not supported) */
  expr::term_ref get_invariant();

  /** Nothing to collect */
  void gc_collect(const expr::gc_relocator& gc_reloc) {}

};

}
}
