/*
 * bitvector.cpp
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */

#include "expr/bitvector.h"

#include <iostream>

namespace sal2 {
namespace expr {

size_t bitvector::hash() const {
  utils::sequence_hash hasher;
  hasher.add(d_gmp_int.get_si());
  hasher.add(d_size);
  return hasher.get();
}

void bitvector::to_stream(std::ostream& out) const {

}

std::ostream& operator << (std::ostream& out, const bitvector& bv) {
  bv.to_stream(out);
  return out;
}

}
}
