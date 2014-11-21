/*
 * rational.cpp
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include "expr/rational.h"
#include "utils/output.h"
#include "utils/hash.h"

#include <cassert>
#include <iostream>

namespace sal2 {
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
  case output::SMTLIB: {
    const mpz_class& num = d_gmp_rat.get_num();
    int sgn = mpz_sgn(num.get_mpz_t());
    if (sgn == 0) {
      out << "0";
    } else {
      out << "(/ ";
      if (sgn < 0) {
        // when printing gmp numerator skip the -, but wrap into (- )
        out << "(- " << (d_gmp_rat.get_num().get_str().c_str() + 1) << ")";
      } else {
        // just regular print
        out << d_gmp_rat.get_num().get_str();
      }
      out << " " << d_gmp_rat.get_den().get_str(10) << ")";
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

}
}
