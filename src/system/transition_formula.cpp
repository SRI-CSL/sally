/*
 * state_transition_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/transition_formula.h"

#include <cassert>
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
: d_tm(tm)
, d_state_type(st)
, d_transition_formula(tm, tf)
{
  assert(st->is_transition_formula(tf));
}

transition_formula::transition_formula(const transition_formula& tf)
: d_tm(tf.d_tm)
, d_state_type(tf.d_state_type)
, d_transition_formula(tf.d_transition_formula)
{
}

}
}
