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

#include "crab.h"

namespace sally {
namespace ai {

crab::crab(const system::context& ctx)
: abstract_interpreter(ctx)
{
  // Construct crab
}

crab::~crab() {
  // Destruct crab
}

void crab::run(system::transition_system* ts) {

  // Run the interpreter


  // Invariant as a term
  expr::term_ref invariant_term;

  // State type has all the transition system variables
  const system::state_type* state_type = ts->get_state_type();

  // Invariant as a state formula
  system::state_formula* invariant = new system::state_formula(tm(), state_type, invariant_term);

  // Attach invariant to the transition system
  ts->add_invariant(invariant);
}

void crab::gc_collect(const expr::gc_relocator& gc_reloc) {
  // Ignore for now
}

}
}
