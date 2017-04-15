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

#include "system/context.h"
#include "ai/ai.h"

namespace sally {
namespace ai {

/**
 * Crab static analyzer.
 */
class crab : public abstract_interpreter {

public:

  /** Construct the interpreter */
  crab(const system::context& ctx);

  /** Destruct the interpreter */
  ~crab();

  /** Run the interpreter on the transition system */
  void run(const system::transition_system* ts, std::vector<system::state_formula*>& out);

  /** Garbage collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);
};

}
}
