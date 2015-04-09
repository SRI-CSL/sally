/*
 * state_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
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
  assert(st->is_state_formula(formula));
}

state_formula::~state_formula() {
}

void state_formula::gc_collect(const expr::gc_info& gc_reloc) {
  gc_reloc.collect(d_state_formula);
}


}
}
