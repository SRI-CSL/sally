/*
 * state_transition_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/transition_formula.h"

using namespace sal2;
using namespace system;

void transition_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << " " << d_transition_formula << "]";
}
