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

#include "system/transition_formula.h"
#include "expr/gc_relocator.h"

#include <cassert>
#include <sstream>
#include <iostream>

namespace sally {
namespace system {

void transition_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << " " << d_transition_formula << "]";
}

std::ostream& operator << (std::ostream& out, const transition_formula& sf) {
  sf.to_stream(out);
  return out;
}

transition_formula::transition_formula(expr::term_manager& tm, const state_type* st, expr::term_ref tf)
: gc_participant(tm)
, d_state_type(st)
, d_transition_formula(tm, tf)
{
  assert(st->is_transition_formula(tf));
}

void transition_formula::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_transition_formula);
}

}
}
