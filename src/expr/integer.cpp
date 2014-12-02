/*
 * integer.cpp
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */


#include "expr/integer.h"

#include <iostream>

namespace sal2 {
namespace expr {

void integer::to_stream(std::ostream& out) const {

}

std::ostream& operator << (std::ostream& out, const integer& z) {
  z.to_stream(out);
  return out;
}

}
}
