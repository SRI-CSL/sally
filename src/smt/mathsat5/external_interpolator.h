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

#pragma once

#ifdef WITH_MATHSAT5

#include <boost/unordered_set.hpp>
#include <mathsat.h>

#include "mathsat5_utils.h"

namespace sally {
namespace smt {

/**
 * External interpolator for mathsat.
 */
class external_interpolator {

  enum interpolation_type {
    INT_STANDARD,
    INT_CONFLICT_RESOLUTION,
    INT_CONFLICT_RESOLUTION_AI
  };

  /** Whether to use the standard interplant */
  interpolation_type d_interpolation_type;

  /** Instance of the internal mathsat */
  size_t d_instance;

  /** MathSAT environment */
  msat_env d_env;

  /** Constant 0 */
  msat_term d_zero;
  /** Constant 1 */
  msat_term d_one;
  /** Constant -1 */
  msat_term d_none;

  typedef boost::unordered_set<msat_term, mathsat5_hasher, mathsat5_eq> msat_term_set;

  /** Atoms from the A part */
  msat_term_set d_A_atoms;

  /** Whether the result is a strict inequality */
  bool d_result_is_strict_inquality;

  /** Process the proof node and return the interpolant */
  msat_term process(msat_proof p);

  /** Combination of two inequalities (a*l1 + b*l2) */
  msat_term process_la_comb(msat_proof p);

  /** Hypothesis inequality */
  msat_term process_la_hyp(msat_proof p);

  /** Hypothesis equality */
  msat_term process_la_hyp_eq(msat_proof p);

  /** Print the proof (debug) */
  void print(std::ostream& out, msat_proof p, std::string indent) const;

  /** Which proof rules we can handle */
  static
  bool can_handle(msat_proof p);

  /** Map from x to x_next */
  term_to_term_map d_variables_AB;

public:

  /**
   * Construct. If use_standard_interpolant = true, it will interpolate against
   * the standard interpolant, otherwise against all of B.
   */
  external_interpolator(size_t instance, msat_env env, std::string interpolation_type);

  /** Note a relationship between x and x' */
  void add_var_pair(msat_term x, msat_term x_next);

  /** Compute the interpolant */
  msat_term compute(msat_term *a, msat_term *b, msat_proof p);

};


}
}

#endif
