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

#include "utils/hash.h"

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
  rational(const mpq_class& gmp_rat) : d_gmp_rat(gmp_rat) { d_gmp_rat.canonicalize(); }
  /** Construct p/q */
  rational(long p, unsigned long q) : d_gmp_rat(p, q) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  rational(const char* s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }
  /** Construct from string representation */
  rational(std::string s): d_gmp_rat(s, 10) { d_gmp_rat.canonicalize(); }

  /** Hash of the rational */
  size_t hash() const;
  /** Compare the two numbers */
  int cmp(const rational& q) const { return mpq_cmp(d_gmp_rat.get_mpq_t(), q.d_gmp_rat.get_mpq_t()); }
  /** Output to stream */
  void to_stream(std::ostream& out) const;

  /** Comparison */
  bool operator == (const rational& q) { return this->cmp(q) == 0; }
};

inline
std::ostream& operator << (std::ostream& out, const rational& q) {
  q.to_stream(out);
  return out;
}

}

namespace hash {

template<>
struct hash<term::rational> {
  size_t operator()(const term::rational& q) const {
    return q.hash();
  }
};

}

}
