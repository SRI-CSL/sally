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
{
  assert(size > 0);
}

bitvector::bitvector(const bitvector& other)
: integer(other)
, d_size(other.d_size)
{
}

/** Construct from integer */
bitvector::bitvector(size_t size, const integer& z)
: integer(z)
, d_size(size)
{
  assert(size > 0);
  assert(z.sgn() >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), size);
  }
}

bitvector::bitvector(size_t size, long x)
: integer(x)
, d_size(size)
{
  assert(size > 0);
  assert(x >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), size);
  }
}

bitvector bitvector::one(size_t size) {
  assert(size > 0);
  return bitvector(size, integer((mpz_class(1) << size) - 1));
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
  assert(d_size > 0);
  assert(sgn() >= 0);
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) > d_size) {
    mpz_fdiv_r_2exp(d_gmp_int.get_mpz_t(), d_gmp_int.get_mpz_t(), d_size);
  }
}

bitvector::bitvector(std::string bits)
: integer(bits, 2)
, d_size(bits.size())
{
  assert(d_size > 0);
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

bool bitvector_sgn_extend::operator == (const bitvector_sgn_extend& other) const {
  return size == other.size;
}

size_t bitvector_sgn_extend::hash() const {
  return size;
}


std::ostream& operator << (std::ostream& out, const bitvector& bv) {
  bv.to_stream(out);
  return out;
}

bitvector& bitvector::set_bit(size_t i, bool value) {
  assert(i < d_size);
  if (value) {
    mpz_setbit(d_gmp_int.get_mpz_t(), i);
  } else {
    mpz_clrbit(d_gmp_int.get_mpz_t(), i);
  }
  return *this;
}

bool bitvector::get_bit(size_t i) const {
  assert(i < d_size);
  return mpz_tstbit(d_gmp_int.get_mpz_t(), i);
}

integer bitvector::get_signed() const {
  if (mpz_sizeinbase(d_gmp_int.get_mpz_t(), 2) == d_size) {
    // The subtraction is integer here
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
  assert(low <= high);
  assert(high < d_size);
  size_t size = high-low+1;
  integer value(d_gmp_int >> low);
  return bitvector(size, value);
}

bool bitvector::uleq(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return *this <= rhs;
}

bool bitvector::sleq(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return get_signed() <= rhs.get_signed();
}

bool bitvector::ult(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return *this < rhs;
}

bool bitvector::slt(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return get_signed() < rhs.get_signed();
}

bool bitvector::ugeq(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return *this >= rhs;
}

bool bitvector::sgeq(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return get_signed() >= rhs.get_signed();
}

bool bitvector::ugt(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return *this > rhs;
}

bool bitvector::sgt(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return get_signed() > rhs.get_signed();
}

bitvector bitvector::add(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return bitvector(d_size, *this + rhs);
}

bitvector bitvector::sub(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  // x + (-y)
  return add(rhs.neg());
}

bitvector bitvector::neg() const {
  return bvnot().add(bitvector(d_size, 1));
}

bitvector bitvector::mul(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return bitvector(d_size, *this * rhs);
}

bitvector bitvector::udiv(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  // unsigned division, truncating towards 0. x/0 = 1...1
  if (rhs.sgn() == 0) {
    return one(d_size);
  } else {
    return bitvector(d_size, integer(d_gmp_int / rhs.d_gmp_int));
  }
}

bitvector bitvector::sdiv(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
//  (bvsdiv s t) abbreviates
//        (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//              (?msb_t ((_ extract |m-1| |m-1|) t)))
//          (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//               (bvudiv s t)                        // D
//          (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//               (bvneg (bvudiv (bvneg s) t))        // B
//          (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//               (bvneg (bvudiv s (bvneg t)))        // C
//               (bvudiv (bvneg s) (bvneg t))))))    // A
  if (msb()) {
    if (rhs.msb()) {
      return neg().udiv(rhs.neg()); // A
    } else {
      return neg().udiv(rhs).neg(); // B
    }
  } else {
    if (rhs.msb()) {
      return udiv(rhs.neg()).neg(); // C
    } else {
      return udiv(rhs);             // D
    }
  }
}

bitvector bitvector::urem(const bitvector& rhs) const {
  // unsigned remainder from truncating division. x = 1...1*0 + y = rem = x
  assert(d_size == rhs.d_size);
  if (rhs.sgn() == 0) {
    return *this;
  } else {
    return bitvector(d_size, integer(d_gmp_int % rhs.d_gmp_int));
  }
}

bitvector bitvector::srem(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
//  (bvsrem s t) abbreviates
//     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//           (?msb_t ((_ extract |m-1| |m-1|) t)))
//       (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//            (bvurem s t)
//       (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//            (bvneg (bvurem (bvneg s) t))
//       (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//            (bvurem s (bvneg t)))
//            (bvneg (bvurem (bvneg s) (bvneg t))))))
  if (msb()) {
    if (rhs.msb()) {
      return neg().urem(rhs.neg()).neg();
    } else {
      return neg().urem(rhs).neg();
    }
  } else {
    if (rhs.msb()) {
      return urem(rhs.neg());
    } else {
      return urem(rhs);
    }
  }
}

bitvector bitvector::smod(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
//  (bvsmod s t) abbreviates
//     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//           (?msb_t ((_ extract |m-1| |m-1|) t)))
//       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
//             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
//         (let ((u (bvurem abs_s abs_t)))
//           (ite (= u (_ bv0 m))
//                u
//           (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//                u
//           (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//                (bvadd (bvneg u) t)
//           (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//                (bvadd u t)
//                (bvneg u))))))))

  // get absolute value
  bitvector abs(*this), rhs_abs(rhs);
  if (msb()) {
    abs.neg();
  }
  if (rhs.msb()) {
    rhs.neg();
  }

  bitvector u = abs.udiv(rhs_abs);
  if (u == bitvector(d_size)) {
    return u;
  } else {
    if (msb()) {
      if (rhs.msb()) {
        return u.neg();
      } else {
        return u.neg().add(rhs);
      }
    } else {
      if (rhs.msb()) {
        return u.add(rhs);
      } else {
        return u;
      }
    }
  }
}

bitvector bitvector::shl(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  if (rhs.d_gmp_int >= d_size) {
    // shift more than size => 0
    return bitvector(d_size);
  } else {
    // concat shift size of zeroes to the right
    size_t shift_size = rhs.get_unsigned();
    if (shift_size == 0) {
      return rhs;
    }
    return bitvector(d_size, concat(bitvector(shift_size)));
  }
}

bitvector bitvector::lshr(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  if (d_size <= rhs.d_gmp_int) {
    // Shift more than size => 0
    return bitvector(d_size);
  } else {
    size_t shift_size = rhs.get_unsigned();
    if (shift_size == 0) {
      return rhs;
    }
    // concat shift size of zeroes to thje left
    return bitvector(d_size, bitvector(shift_size).concat(extract(shift_size, d_size - 1)));
  }
}

bitvector bitvector::ashr(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  if (d_size <= rhs.d_gmp_int) {
    // Shift more than size => 0 or 1 depending on top bit
    if (get_bit(d_size-1)) {
      return one(d_size);
    } else {
      return bitvector(d_size);
    }
  } else {
    size_t shift_size = rhs.get_unsigned();
    if (shift_size == 0) {
      return rhs;
    }
    // What to pad with
    bitvector pad(d_size);
    if (get_bit(d_size-1)) {
      pad = one(d_size);
    }
    // concat shift size of zeroes to thje left
    return bitvector(d_size, pad.concat(extract(shift_size, d_size - 1)));
  }
}

bitvector bitvector::bvxor(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return bitvector(d_size, integer(d_gmp_int ^ rhs.d_gmp_int));
}

bitvector bitvector::bvand(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return bitvector(d_size, integer(d_gmp_int & rhs.d_gmp_int));
}

bitvector bitvector::bvor(const bitvector& rhs) const {
  assert(d_size == rhs.d_size);
  return bitvector(d_size, integer(d_gmp_int | rhs.d_gmp_int));
}

bitvector bitvector::bvnot() const {
  return bvxor(one(d_size));
}

}
}
