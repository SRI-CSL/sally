/*
 * bitvector.cpp
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */

#include "expr/bitvector.h"
#include "utils/output.h"

#include <iostream>
#include <cassert>

namespace sally {
namespace expr {

bitvector::bitvector(size_t size)
: d_size(size)
{}

/** Construct from integer */
bitvector::bitvector(size_t size, const integer& z)
: integer(z)
, d_size(size)
{}

bitvector::bitvector(size_t size, long x)
: integer(x)
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
  output::language lang = output::get_output_language(out);
  switch (lang) {
  case output::MCMT:
  case output::HORN:
  {
    out << "(_ bv";
    integer::to_stream(out);
    out  << " " << size() << ")";
    break;
  }
  case output::NUXMV:
    out << "0d" << d_size << d_gmp_int.get_str();
    break;
  default:
    assert(false);
  }
}


bool bitvector_extract::operator == (const bitvector_extract& other) const {
  return high == other.high && low == other.low;
}

size_t bitvector_extract::hash() const {
  utils::sequence_hash hasher;
  hasher.add(high);
  hasher.add(low);
  return hasher.get();
}

std::ostream& operator << (std::ostream& out, const bitvector& bv) {
  bv.to_stream(out);
  return out;
}

}
}
