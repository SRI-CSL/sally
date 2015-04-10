/*
 * state_transition_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
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
