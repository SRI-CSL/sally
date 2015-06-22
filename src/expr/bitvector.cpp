/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
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
