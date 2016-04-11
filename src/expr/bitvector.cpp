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
{
  assert(z.sgn() >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), size);
  }
}

bitvector::bitvector(size_t size, long x)
: integer(x)
, d_size(size)
{
  assert(x >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), size);
  }
}

size_t bitvector::hash() const {
  utils::sequence_hash hasher;
  hasher.add(d_gmp_int.get_ui());
  hasher.add(d_size);
  return hasher.get();
}

bitvector::bitvector(const char* bits)
: integer(bits, 2)
, d_size(strlen(bits))
{
  assert(sgn() >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > d_size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), d_size);
  }
}

bitvector::bitvector(std::string bits)
: integer(bits, 2)
, d_size(bits.size())
{
  assert(sgn() >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > d_size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), d_size);
  }
}

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

bitvector& bitvector::set_bit(size_t i, bool value) {
  if (value) {
    mpz_setbit(d_gmp_int.get_mpz_t(), i);
  } else {
    mpz_clrbit(d_gmp_int.get_mpz_t(), i);
  }
  return *this;
}

integer bitvector::get_signed() const {
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) == d_size) {
    return bitvector(d_size-1, d_gmp_int) - bitvector(d_size).set_bit(d_size-1, true);
  } else {
    // No first bit
    return d_gmp_int;
  }
}

bitvector bitvector::concat(const bitvector& rhs) const {
  size_t size = d_size + rhs.d_size;
  integer value((d_gmp_int << rhs.d_size) + rhs.d_gmp_int);
  return bitvector(size, value);
}

bitvector bitvector::extract(size_t low, size_t high) const {
  size_t size = high-low+1;
  integer value(d_gmp_int >> low);
  return bitvector(size, value);
}

bool bitvector::uleq(const bitvector& rhs) const {
  return *this <= rhs;
}

bool bitvector::sleq(const bitvector& rhs) const {
  return get_signed() <= rhs.get_signed();
}

bool bitvector::ult(const bitvector& rhs) const {
  return *this < rhs;
}

bool bitvector::slt(const bitvector& rhs) const {
  return get_signed() < rhs.get_signed();
}

bool bitvector::ugeq(const bitvector& rhs) const {
  return *this >= rhs;
}

bool bitvector::sgeq(const bitvector& rhs) const {
  return get_signed() >= rhs.get_signed();
}

bool bitvector::ugt(const bitvector& rhs) const {
  return *this > rhs;
}

bool bitvector::sgt(const bitvector& rhs) const {
  return get_signed() > rhs.get_signed();
}

}
}
