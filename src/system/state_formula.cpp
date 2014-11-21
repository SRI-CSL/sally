/*
 * state_formula.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/state_formula.h"

#include <iostream>

using namespace sal2;
using namespace system;

void state_formula::to_stream(std::ostream& out) const {
  out << "[" << *d_state_type << ": " << d_state_formula << "]";
}

