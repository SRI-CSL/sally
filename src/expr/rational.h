/*
 * rational.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <gmpxx.h>
#include <string>
#include <iostream>

namespace sal2 {
namespace term {

class rational {
  mpq_class d_gmp_rat;
public:
  rational(): d_gmp_rat(0) { d_gmp_rat.canonicalize(); }
  rational(const mpq_class& gmp_rat) : d_gmp_rat(gmp_rat) {}
  rational(long p, unsigned long q) : d_gmp_rat(p, q) { d_gmp_rat.canonicalize(); }
  rational(const char* s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  rational(std::string s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  rational(const rational& q): d_gmp_rat(q.d_gmp_rat) { d_gmp_rat.canonicalize(); }
  std::string to_string() const;
  void to_stream(std::ostream& out) const;
};

}
}
