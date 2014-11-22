/*
 * state_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/state_formula.h"

#include <iostream>

namespace sal2 {
namespace system {

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << ": " << d_state_formula << "]";
}

std::ostream& operator << (std::ostream& out, const state_formula& sf) {
  sf.to_stream(out);
  return out;
}

}
}
