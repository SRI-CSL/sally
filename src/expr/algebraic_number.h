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

#include <cstddef>
#include <string>
#include <iosfwd>

#include <poly/algebraic_number.h>

#include "utils/hash.h"

#include "expr/integer.h"
#include "expr/rational.h"

namespace sally {
namespace expr {

class term_ref;
class term_manager;

/**
 * Wrapper around the GMP algebraic_number.
 */
class algebraic_number {

  /** How many bits of precision for hashing */
  static const unsigned hash_precision = 5;

  /** The GMP object */
  lp_algebraic_number_t d_a;

public:

  /** Default construct a 0 */
  algebraic_number();
  /** Construct from libpoly algebraic number */
  algebraic_number(const lp_algebraic_number_t* a);
  /** Copy construct */
  algebraic_number(const algebraic_number& a);
  /** Construct from integer  */
  algebraic_number(const integer& z);
  /** Construct from rational  */
  algebraic_number(const rational& q);

  /** Destructor */
  ~algebraic_number();

  /** Hash of the algebraic_number */
  size_t hash() const;

  /** Compare the two numbers */
  int cmp(const algebraic_number& other) const;

  /** Output to stream */
  void to_stream(std::ostream& out) const;

  /** Comparison */
  bool operator == (const algebraic_number& q) const;

  // Arithmetic

  algebraic_number operator + (const algebraic_number& other) const;
  algebraic_number operator + (const integer& other) const;
  algebraic_number& operator += (const algebraic_number& other);
  algebraic_number& operator += (const integer& other);

  algebraic_number operator - () const;
  algebraic_number operator - (const algebraic_number& other) const;
  algebraic_number& operator -= (const algebraic_number& other);

  algebraic_number operator * (const algebraic_number& other) const;
  algebraic_number& operator *= (const algebraic_number& other);

  algebraic_number operator / (const algebraic_number& other) const;
  algebraic_number& operator /= (const algebraic_number& other);

  bool operator < (const algebraic_number& other) const;
  bool operator <= (const algebraic_number& other) const;
  bool operator > (const algebraic_number& other) const;
  bool operator >= (const algebraic_number& other) const;

  /** Assignment */
  algebraic_number& operator = (const algebraic_number& z);

  /** Returns true if it's an integer */
  bool is_integer() const;

  /** Returns true if it's a rational */
  bool is_rational() const;

  /** Returns the sign of the number */
  int sgn() const;

  /** Returns the inverse of the algebraic_number, i.e. 1/q */
  algebraic_number invert() const;

  /** Negate, i.e. -Q */
  algebraic_number negate() const;

  /** Get floor */
  integer floor() const;

  /** Get ceiling */
  integer ceiling() const;

  /** Get the libpoly representation */
  const lp_algebraic_number_t* a() const {
    return &d_a;
  }

  /** Return rational approximation */
  rational approx() const;
};

/** Output operator */
std::ostream& operator << (std::ostream& out, const algebraic_number& q);

}

namespace utils {

template<>
struct hash<expr::algebraic_number> {
  size_t operator()(const expr::algebraic_number& q) const {
    return q.hash();
  }
};

}

}
