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

#include "system/state_formula.h"
#include "expr/gc_relocator.h"

#include <iostream>
#include <sstream>
#include <cassert>

namespace sally {
namespace system {

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << ": " << d_state_formula << "]";
}

std::ostream& operator << (std::ostream& out, const state_formula& sf) {
  sf.to_stream(out);
  return out;
}

state_formula::state_formula(expr::term_manager& tm, const state_type* st, expr::term_ref formula)
: gc_participant(tm)
, d_state_type(st)
, d_state_formula(tm, formula)
{
  assert(st->is_state_formula(formula, true));
}

state_formula::~state_formula() {
}

void state_formula::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_state_formula);
}


}
}
