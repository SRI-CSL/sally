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

#pragma once

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>
#include "../../system/trace_helper.h"

namespace sally {
namespace bmc {

/**
 * Bounded model checking engine.
 */
class bmc_engine : public engine {

  /** The trace we're building */
  system::trace_helper* d_trace;

public:

  bmc_engine(const system::context& ctx);
  ~bmc_engine();

  /** Query */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::trace_helper* get_trace();

  /** Invariant (not supported) */
  invariant get_invariant();

  /** Nothing to collect */
  void gc_collect(const expr::gc_relocator& gc_reloc) {}
};

}
}
