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

#include <gmpxx.h>
#include <string>
#include <iosfwd>

#include "utils/hash.h"
#include "expr/integer.h"

namespace sally {
namespace expr {

class term_ref;
class term_manager;

/**
 * Wrapper around the GMP rational.
 */
class rational {
  /** The GMP object */
  mpq_class d_gmp_rat;
public:
  /** Default construct a 0 */
  rational(): d_gmp_rat(0) { d_gmp_rat.canonicalize(); }
  /** Copy construct */
  rational(const rational& q): d_gmp_rat(q.d_gmp_rat) { d_gmp_rat.canonicalize(); }
  /** Construct from GMP */
  rational(const mpq_class& gmp_rat) : d_gmp_rat(gmp_rat) { d_gmp_rat.canonicalize(); }
  /** Construct from GMP */
  rational(mpq_t gmp_rat): d_gmp_rat(gmp_rat) { d_gmp_rat.canonicalize(); }
  /** Construct from GMP integer */
  rational(mpz_t gmp_z): d_gmp_rat(mpz_class(gmp_z)) { d_gmp_rat.canonicalize(); }
  /** Construct p/q */
  rational(const integer& p, const integer& q): d_gmp_rat(p.mpz(), q.mpz()) { d_gmp_rat.canonicalize(); }
  /** Construct p/q */
  rational(long p, unsigned long q) : d_gmp_rat(p, q) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  explicit rational(const char* s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  explicit rational(std::string s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation "1" "2" = 1.2 = 3/2 */
  rational(std::string integer_part, std::string fractional_part)
  : d_gmp_rat(integer(integer_part + fractional_part, 10).mpz(), integer(10).pow(fractional_part.size()).mpz())
  { d_gmp_rat.canonicalize(); }

  /** Cosntruct from constant integer or rational term */
  rational(const term_manager& tm, term_ref t);

  /** Hash of the rational */
  size_t hash() const;
  /** Compare the two numbers */
  int cmp(const rational& q) const { return mpq_cmp(d_gmp_rat.get_mpq_t(), q.d_gmp_rat.get_mpq_t()); }

  /** Output to stream */
  void to_stream(std::ostream& out) const;

  /** Comparison */
  bool operator == (const rational& q) const { return this->cmp(q) == 0; }

  // Arithmetic

  rational operator + (const rational& other) const;
  rational operator + (const integer& other) const;
  rational& operator += (const rational& other);
  rational& operator += (const integer& other);

  rational operator - () const;
  rational operator - (const rational& other) const;
  rational operator - (const integer& other) const;
  rational& operator -= (const rational& other);
  rational& operator -= (const integer& other);

  rational operator * (const rational& other) const;
  rational operator * (const integer& other) const;
  rational& operator *= (const rational& other);
  rational& operator *= (const integer& other);

  rational operator / (const rational& other) const;
  rational operator / (const integer& other) const;
  rational& operator /= (const rational& other);
  rational& operator /= (const integer& other);

  bool operator < (const rational& other) const;
  bool operator <= (const rational& other) const;
  bool operator > (const rational& other) const;
  bool operator >= (const rational& other) const;

  /** Assignment for integers */
  rational& operator = (const integer& z);

  /** Returns true if it's an integer */
  bool is_integer() const;

  /** Returns the sign of the number */
  int sgn() const;

  /** Returns the numerator */
  integer get_numerator() const;

  /** Returns the denominator */
  integer get_denominator() const;

  /** Returns the inverse of the rational, i.e. 1/q */
  rational invert() const;

  /** Negate, i.e. -Q */
  rational negate() const;

  /** Get floor */
  rational floor() const;

  /** Get ceiling */
  rational ceiling() const;

  /** Get a simple value in (a, b) */
  static
  rational value_between(const rational& a, const rational& b);

  const mpq_class& mpq() const {
    return d_gmp_rat;
  }
};

/** Output operator */
std::ostream& operator << (std::ostream& out, const rational& q);

}

namespace utils {

template<>
struct hash<expr::rational> {
  size_t operator()(const expr::rational& q) const {
    return q.hash();
  }
};

}

}
