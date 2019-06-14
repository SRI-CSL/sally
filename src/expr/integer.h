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
#include <cstddef>
#include <gmpxx.h>

#include "utils/hash.h"

namespace sally {
namespace expr {

class term_ref;
class term_manager;

class rational;

class integer {

protected:

  /** Gmp object */
  mpz_class d_gmp_int;

public:

  /** Default construct a 0 */
  integer(): d_gmp_int(0) {}
  /** Copy construct */
  integer(const integer& z): d_gmp_int(z.d_gmp_int) {}
  /** Construct from GMP */
  integer(const mpz_class& z) : d_gmp_int(z) {}
  /** Construct from GMP */
  integer(mpz_t z) : d_gmp_int(z) {}
  /** Construct from long */
  integer(long z) : d_gmp_int(z) {}
  /** Construct from string representation */
  integer(const char* s, size_t base): d_gmp_int(s, base) {}
  /** Construct from string representation */
  integer(std::string s, size_t base): d_gmp_int(s, base) {}
  /** Construct from rational: round_up ? ceil : floor */
  integer(const rational& q, bool round_up = false);

  // Arithmetic

  integer operator + (const integer& other) const;
  integer& operator += (const integer& other);

  integer operator - () const;
  integer operator - (const integer& other) const;
  integer& operator -= (const integer& other);

  integer operator * (const integer& other) const;
  integer& operator *= (const integer& other);

  bool operator < (const integer& other) const;
  bool operator <= (const integer& other) const;
  bool operator > (const integer& other) const;
  bool operator >= (const integer& other) const;

  integer pow(unsigned long n) const;

  /** Get the sign */
  int sgn() const;

  /** Get unsigned value */
  unsigned long get_unsigned() const;

  /** Get signed value */
  signed long get_signed() const;

  /** Returns the hash of the integer */
  size_t hash() const { return d_gmp_int.get_si(); }

  /** Compare the two numbers */
  int cmp(const integer& other) const { return mpz_cmp(d_gmp_int.get_mpz_t(), other.d_gmp_int.get_mpz_t()); }

  /** Compare */
  bool operator == (const integer& other) const { return cmp(other) == 0; }

  /** Output ot stream */
  void to_stream(std::ostream& out) const;

  const mpz_class& mpz() const {
    return d_gmp_int;
  }
};

std::ostream& operator << (std::ostream& out, const integer& z);

}

namespace utils {

template<>
struct hash<expr::integer> {
  size_t operator()(const expr::integer& z) const {
    return z.hash();
  }
};

}
}
