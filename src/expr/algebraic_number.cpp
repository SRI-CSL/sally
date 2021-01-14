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

#include "algebraic_number.h"

#include <poly/rational.h>

#include "expr/integer.h"
#include "utils/output.h"
#include "utils/hash.h"

#include "expr/term_manager.h"

#include <cassert>
#include <iostream>
namespace sally {
namespace expr {

algebraic_number::algebraic_number() {
  lp_algebraic_number_construct_zero(&d_a);
}

algebraic_number::algebraic_number(const lp_algebraic_number_t* a) {
  lp_algebraic_number_construct_copy(&d_a, a);
}

algebraic_number::algebraic_number(const algebraic_number& a) {
  lp_algebraic_number_construct_copy(&d_a, &a.d_a);
}

algebraic_number::algebraic_number(const integer& z) {
  lp_algebraic_number_construct_from_integer(&d_a, z.mpz().get_mpz_t());
}

algebraic_number::algebraic_number(const rational& q) {
  lp_algebraic_number_construct_from_rational(&d_a, q.mpq().get_mpq_t());
}

algebraic_number::~algebraic_number() {
  lp_algebraic_number_destruct(&d_a);
}

size_t algebraic_number::hash() const {
  return lp_algebraic_number_hash_approx(&d_a, hash_precision);
}

void algebraic_number::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  switch (lang) {
  case output::MCMT:
  case output::MCMT_TAB:
  case output::HORN:
  {
    out << "(algebraic_number " << lp_algebraic_number_to_string(&d_a) << ")";
    break;
  }
  case output::NUXMV: {
    out << "(algebraic_number " << lp_algebraic_number_to_string(&d_a) << ")";
    break;
  }
  default:
    assert(false);
  }
}

std::ostream& operator << (std::ostream& out, const algebraic_number& q) {
  q.to_stream(out);
  return out;
}

bool algebraic_number::is_integer() const {
  return lp_algebraic_number_is_integer(&d_a);
}

algebraic_number algebraic_number::invert() const {
  algebraic_number result;
  lp_algebraic_number_inv(&result.d_a, &d_a);
  return result;
}

algebraic_number algebraic_number::negate() const {
  algebraic_number result;
  lp_algebraic_number_neg(&result.d_a, &d_a);
  return result;
}

integer algebraic_number::floor() const {
  lp_integer_t lp_result;
  lp_integer_construct(&lp_result);
  lp_algebraic_number_floor(&d_a, &lp_result);
  integer result(&lp_result);
  lp_integer_destruct(&lp_result);
  return result;
}

integer algebraic_number::ceiling() const {
  lp_integer_t lp_result;
  lp_integer_construct(&lp_result);
  lp_algebraic_number_ceiling(&d_a, &lp_result);
  integer result(&lp_result);
  lp_integer_destruct(&lp_result);
  return result;
}

int algebraic_number::sgn() const {
  return lp_algebraic_number_sgn(&d_a);
}

algebraic_number& algebraic_number::operator = (const algebraic_number& other) {
  if (this != &other) {
    lp_algebraic_number_destruct(&d_a);
    lp_algebraic_number_construct_copy(&d_a, &other.d_a);
  }
  return *this;
}

algebraic_number algebraic_number::operator + (const algebraic_number& other) const {
  algebraic_number result;
  lp_algebraic_number_add(&result.d_a, &d_a, &other.d_a);
  return result;
}

algebraic_number& algebraic_number::operator += (const algebraic_number& other) {
  lp_algebraic_number_add(&d_a, &d_a, &other.d_a);
  return *this;
}

algebraic_number algebraic_number::operator - () const {
  algebraic_number result;
  lp_algebraic_number_neg(&result.d_a, &d_a);
  return result;
}

algebraic_number algebraic_number::operator - (const algebraic_number& other) const {
  algebraic_number result;
  lp_algebraic_number_sub(&result.d_a, &d_a, &other.d_a);
  return result;
}


algebraic_number& algebraic_number::operator -= (const algebraic_number& other) {
  lp_algebraic_number_sub(&d_a, &d_a, &other.d_a);
  return *this;
}

algebraic_number algebraic_number::operator * (const algebraic_number& other) const {
  algebraic_number result;
  lp_algebraic_number_mul(&result.d_a, &d_a, &other.d_a);
  return result;
}

algebraic_number& algebraic_number::operator *= (const algebraic_number& other) {
  lp_algebraic_number_mul(&d_a, &d_a, &other.d_a);
  return *this;
}

algebraic_number algebraic_number::operator / (const algebraic_number& other) const {
  algebraic_number result;
  lp_algebraic_number_div(&result.d_a, &d_a, &other.d_a);
  return result;
}

algebraic_number& algebraic_number::operator /= (const algebraic_number& other) {
  lp_algebraic_number_div(&d_a, &d_a, &other.d_a);
  return *this;
}

bool algebraic_number::operator == (const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a) == 0;
}

bool algebraic_number::operator < (const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a) < 0;
}

bool algebraic_number::operator <= (const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a) <= 0;
}

bool algebraic_number::operator > (const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a) > 0;
}

bool algebraic_number::operator >= (const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a) >= 0;
}

int algebraic_number::cmp(const algebraic_number& other) const {
  return lp_algebraic_number_cmp(&d_a, &other.d_a);
}

rational algebraic_number::approx() const {
  lp_rational_t q;
  lp_rational_construct(&q);
  lp_algebraic_number_to_rational(&d_a, &q);
  rational result(&q);
  lp_rational_destruct(&q);
  return result;
}

}
}

