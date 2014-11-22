/*
 * state_transition_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/transition_formula.h"

#include <iostream>

namespace sal2 {
namespace system {

void transition_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << " " << d_transition_formula << "]";
}

std::ostream& operator << (std::ostream& out, const transition_formula& sf) {
  sf.to_stream(out);
  return out;
}

}
}
