/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "expr/state.h"

using namespace sal2;
using namespace expr;

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_formula << "]";
}

void state_transition_formula::to_stream(std::ostream& out) const {
  out << "[" << d_state_type << " " << d_transition_formula << "]";
}

