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

#pragma once

#include <iosfwd>
#include "expr/integer.h"
#include "utils/hash.h"

namespace sally {
namespace expr {

class bitvector : public integer {

  /** The size in bits */
  size_t d_size;

public:

  /** Construct 0 of size 1 */
  bitvector(): d_size(1) {}

  /** Construct 0 */
  explicit bitvector(size_t size);

  /** Construct from integer */
  bitvector(size_t size, const integer& z);

  /** Construct from int */
  bitvector(size_t size, long x);

  /** Construct from a string representation (0 terminated) */
  explicit bitvector(const char* bits);

  /** Construct from a string representation */
  explicit bitvector(std::string bits);

  /** Get the size of the bitvector */
  size_t size() const { return d_size; }

  /** Hash */
  size_t hash() const;

  /** Compare */
  bool operator == (const bitvector& other) const {
    return d_size == other.d_size && cmp(other) == 0;
  }

  /** Output ot stream */
  void to_stream(std::ostream& out) const;

  const mpz_class& mpz() const {
    return d_gmp_int;
  }
};

/**
 * Payload for bitvector extract operation (low <= high).
 */
struct bitvector_extract {
  /** High bit to be extracted */
  size_t high;
  /** Low bit to be extracted */
  size_t low;

  bitvector_extract(size_t high, size_t low)
  : high(high), low(low) {}

  /** Comparison */
  bool operator == (const bitvector_extract& other) const;

  /** Hash */
  size_t hash() const;
};

std::ostream& operator << (std::ostream& out, const bitvector& bv);

}

namespace utils {

template<>
struct hash<expr::bitvector> {
  size_t operator()(const expr::bitvector& bv) const {
    return bv.hash();
  }
};

template<>
struct hash<expr::bitvector_extract> {
  size_t operator()(const expr::bitvector_extract& extract) const {
    return extract.hash();
  }
};

}
}
