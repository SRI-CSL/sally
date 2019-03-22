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

#include "expr/rational.h"
#include "expr/integer.h"
#include "utils/output.h"
#include "utils/hash.h"

#include "expr/term_manager.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace expr {

size_t rational::hash() const {
  utils::sequence_hash hasher;
  hasher.add(mpz_get_si(d_gmp_rat.get_den_mpz_t()));
  hasher.add(mpz_get_si(d_gmp_rat.get_num_mpz_t()));
  return hasher.get();
}

void rational::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  switch (lang) {
  case output::MCMT:
  case output::HORN:
  {
    const mpz_class& num = d_gmp_rat.get_num();
    int sgn = mpz_sgn(num.get_mpz_t());
    if (sgn == 0) {
      out << "0";
    } else {
      bool is_rational = !is_integer();
      if (is_rational) {
        out << "(/ ";
      }
      if (sgn < 0) {
        // when printing gmp numerator skip the -, but wrap into (- )
        out << "(- " << (d_gmp_rat.get_num().get_str().c_str() + 1) << ")";
      } else {
        // just regular print
        out << d_gmp_rat.get_num().get_str();
      }
      if (is_rational) {
        out << " " << d_gmp_rat.get_den().get_str(10) << ")";
      }
    }
    break;
  }
  case output::NUXMV: {
    int sign = sgn();
    if (sign == 0) {
      out << "0";
    } else if (sign > 0) {
      if (is_integer()) {
        // Integer output
        out << "f'" << d_gmp_rat.get_str(10) << "/1";
      } else {
        // Rational output
        out << "f'" << d_gmp_rat.get_str(10);
      }
    } else {
      out << "-" << negate();
    }
    break;
  }
  default:
    assert(false);
  }
}

// Simply method to create rationals also from numbers with decimal point. TODO: write tests
expr::rational decimal2rational(std::string decimal) {
//  std::cout << decimal << std::endl;
  size_t pos = decimal.find('.');
  assert(pos != std::string::npos);
  if (pos == std::string::npos) {
    return expr::rational(decimal);
  }
  assert(pos < decimal.size());
  size_t len_after_point = decimal.size() - pos - 1;
  decimal.erase(pos, 1);
  decimal.push_back('/');
  decimal.push_back('1');
  for (size_t i = 0; i < len_after_point; ++i) {
    decimal.push_back('0');
  }
  expr::rational res(decimal);
//  std::cout << res << std::endl;
  return res;
}

std::ostream& operator << (std::ostream& out, const rational& q) {
  q.to_stream(out);
  return out;
}

bool rational::is_integer() const {
  const mpz_class& den = d_gmp_rat.get_den();
  return den == 1;
}

rational rational::invert() const {
  return rational(1 / d_gmp_rat);
}

rational rational::negate() const {
  return rational(-d_gmp_rat);
}

rational rational::floor() const {
  return rational(integer(*this, false), integer(1));
}

rational rational::ceiling() const {
  return rational(integer(*this, true), integer(1));
}

int rational::sgn() const {
  return mpq_sgn(d_gmp_rat.get_mpq_t());
}

integer rational::get_numerator() const {
  return integer(d_gmp_rat.get_num());
}

integer rational::get_denominator() const {
  return integer(d_gmp_rat.get_den());
}


rational& rational::operator = (const integer& z) {
  d_gmp_rat = z.mpz();
  d_gmp_rat.canonicalize();
  return *this;
}

rational rational::operator + (const rational& other) const {
  return rational(d_gmp_rat + other.d_gmp_rat);
}

rational rational::operator + (const integer& other) const {
  return rational(d_gmp_rat + other.mpz());
}

rational& rational::operator += (const rational& other) {
  d_gmp_rat += other.d_gmp_rat;
  d_gmp_rat.canonicalize();
  return *this;
}

rational& rational::operator += (const integer& other) {
  d_gmp_rat += other.mpz();
  d_gmp_rat.canonicalize();
  return *this;
}

rational rational::operator - () const {
  return rational(-d_gmp_rat);
}

rational rational::operator - (const rational& other) const {
  return rational(d_gmp_rat - other.d_gmp_rat);
}

rational rational::operator - (const integer& other) const {
  return rational(d_gmp_rat - other.mpz());
}

rational& rational::operator -= (const rational& other) {
  d_gmp_rat -= other.d_gmp_rat;
  d_gmp_rat.canonicalize();
  return *this;
}

rational& rational::operator -= (const integer& other) {
  d_gmp_rat -= other.mpz();
  d_gmp_rat.canonicalize();
  return *this;
}

rational rational::operator * (const rational& other) const {
  return rational(d_gmp_rat * other.d_gmp_rat);
}

rational rational::operator * (const integer& other) const {
  return rational(d_gmp_rat * other.mpz());
}

rational& rational::operator *= (const rational& other) {
  d_gmp_rat *= other.d_gmp_rat;
  d_gmp_rat.canonicalize();
  return *this;
}

rational& rational::operator *= (const integer& other) {
  d_gmp_rat *= other.mpz();
  d_gmp_rat.canonicalize();
  return *this;
}


rational rational::operator / (const rational& other) const {
  return rational(d_gmp_rat / other.d_gmp_rat);
}

rational rational::operator / (const integer& other) const {
  return rational(d_gmp_rat / other.mpz());
}

rational& rational::operator /= (const rational& other) {
  d_gmp_rat /= other.d_gmp_rat;
  d_gmp_rat.canonicalize();
  return *this;
}

rational& rational::operator /= (const integer& other) {
  d_gmp_rat /= other.mpz();
  d_gmp_rat.canonicalize();
  return *this;
}

bool rational::operator < (const rational& other) const {
  return d_gmp_rat < other.d_gmp_rat;
}

bool rational::operator <= (const rational& other) const {
  return d_gmp_rat <= other.d_gmp_rat;
}

bool rational::operator > (const rational& other) const {
  return d_gmp_rat > other.d_gmp_rat;
}

bool rational::operator >= (const rational& other) const {
  return d_gmp_rat >= other.d_gmp_rat;
}

rational::rational(const term_manager& tm, term_ref t) {
  const term& t_term = tm.term_of(t);
  *this = tm.get_rational_constant(t_term);
}

rational rational::value_between(const rational& a, const rational& b) {
  return (a + b) / 2;
}


}
}

