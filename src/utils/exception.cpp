/*
 * exception.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "utils/exception.h"

#include <iostream>

namespace sal2 {

void exception::to_stream(std::ostream& out) const {
  out << d_msg;
}


std::ostream& operator << (std::ostream& out, const exception& e) {
  e.to_stream(out);
  return out;
}

}

