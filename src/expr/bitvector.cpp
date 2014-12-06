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

bitvector::bitvector(size_t size)
: d_size(size)
{}

/** Construct from integer */
bitvector::bitvector(size_t size, const integer& z)
: integer(z)
, d_size(size)
{}

size_t bitvector::hash() const {
  utils::sequence_hash hasher;
  hasher.add(d_gmp_int.get_ui());
  hasher.add(d_size);
  return hasher.get();
}

bitvector::bitvector(const char* bits)
: integer(bits, 2)
, d_size(strlen(bits))
{}

bitvector::bitvector(std::string bits)
: integer(bits, 2)
, d_size(bits.size())
{}

void bitvector::to_stream(std::ostream& out) const {
  out << "(_ bv" << size() << " ";
  integer::to_stream(out);
  out << ")";
}

std::ostream& operator << (std::ostream& out, const bitvector& bv) {
  bv.to_stream(out);
  return out;
}

}
}
