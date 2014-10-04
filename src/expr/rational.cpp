/*
 * rational.cpp
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include "expr/rational.h"
#include "utils/output.h"

#include <cassert>

using namespace std;
using namespace sal2;
using namespace term;

std::string rational::to_string() const {
  return d_gmp_rat.get_str();
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
        out << "(- " << (++ d_gmp_rat.get_num().get_str().c_str()) << ")";
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



