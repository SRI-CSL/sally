/*
 * rational.cpp
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include "expr/rational.h"
#include "expr/integer.h"
#include "utils/output.h"
#include "utils/hash.h"

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
      out << "f'" << d_gmp_rat.get_str(10);
    } else {
      out << "-" << negate();
    }
    break;
  }
  default:
    assert(false);
  }
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

}
}
