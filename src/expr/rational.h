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
  rational(const mpq_class& gmp_rat) : d_gmp_rat(gmp_rat) {}
  /** Construct p/q */
  rational(long p, unsigned long q) : d_gmp_rat(p, q) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  rational(const char* s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  rational(std::string s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }

  /** Hash of the rational */
  size_t hash() const { return 0; }
  /** Output to stream */
  void to_stream(std::ostream& out) const;
};

inline
std::ostream& operator << (std::ostream& out, const rational& q) {
  q.to_stream(out);
  return out;
}

}
}
