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

#ifdef WITH_MATHSAT5

#include "external_interpolator.h"
#include "conflict_resolution.h"

#include "utils/trace.h"

#include <cassert>
#include <string>
#include <iostream>

namespace sally {
namespace smt {

external_interpolator::external_interpolator(size_t instance, msat_env env, bool use_standard_interpolant)
: d_use_standard_interpolant(use_standard_interpolant)
, d_instance(instance)
, d_env(env)
, d_result_is_strict_inquality(false)
{
  d_zero = msat_make_number(env, "0");
  d_one = msat_make_number(env, "1");
  d_none = msat_make_number(env, "-1");
}

msat_term external_interpolator::compute(msat_term *a, msat_term *b, msat_proof p) {

  TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: computing interpolant." << std::endl;

  size_t i;

  msat_term standard_interpolant;
  MSAT_MAKE_ERROR_TERM(standard_interpolant);

  if (output::trace_tag_is_enabled("mathsat5::extitp")) {
    for (i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
      msat_term l = a[i];
      char* str = msat_term_repr(l);
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: a[" << i << "]:" << str << std::endl;
      msat_free(str);
    }
    for (i = 0; !MSAT_ERROR_TERM(b[i]); ++ i) {
      msat_term l = b[i];
      char* str = msat_term_repr(l);
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: b[" << i << "]:" << str << std::endl;
      msat_free(str);
    }
  }

  if (d_use_standard_interpolant) {
    // Remember the A part
    d_A_atoms.clear();
    for (i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
      msat_term l = a[i];
      if (msat_term_is_not(d_env, l)) {l = msat_term_get_arg(l, 0);}
      d_A_atoms.insert(l);
    }

    // Compute the standard interpolant
    d_result_is_strict_inquality = false;
    msat_term interpolant_term = process(p);
    if (MSAT_ERROR_TERM(interpolant_term)) {
      return interpolant_term;
    }
    if (d_result_is_strict_inquality) {
      standard_interpolant = msat_make_not(d_env, msat_make_leq(d_env, d_zero, interpolant_term));
    } else {
      standard_interpolant = msat_make_leq(d_env, interpolant_term, d_zero);
    }

    if (output::trace_tag_is_enabled("mathsat5::extitp")) {
      char* str = msat_term_repr(standard_interpolant);
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: standard interpolant: " << str << std::endl;
      msat_free(str);
    }
  }

  // Do conflict resolution
  conflict_resolution cr(d_env);
  msat_term final_interpolant = d_use_standard_interpolant ?
      cr.interpolate(a, msat_make_not(d_env, standard_interpolant)) :
      cr.interpolate(a, b);
  if (MSAT_ERROR_TERM(final_interpolant)) {
    final_interpolant = standard_interpolant;
  }

  if (output::trace_tag_is_enabled("mathsat5::extitp")) {
    char* str = msat_term_repr(final_interpolant);
    TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: final interpolant: " << str << std::endl;
    msat_free(str);
  }

  return final_interpolant;
}

msat_term external_interpolator::process(msat_proof p) {
  msat_term result;

  // Handle or proof cases separately.
  std::string name = msat_proof_get_name(p);
  if (name == "la-comb") {
    result = process_la_comb(p);
  } else if (name == "la-hyp") {
    result = process_la_hyp(p);
  } else if (name == "la-hyp-eq") {
    result = process_la_hyp_eq(p);
  } else {
    if (name == "la-neq") {
      assert(false);
    }
    TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: unhandled proof rule: " << name << std::endl;
    msat_term err;
    MSAT_MAKE_ERROR_TERM(err);
    return err;
  }

  // Return the standard interpolant
  return result;
}

msat_term external_interpolator::process_la_comb(msat_proof p) {
  assert(msat_proof_get_arity(p) == 4);

  // (a, l1, b, l2) = a*l1 + b*l2
  // => Just add the A parts

  // Get the coefficients
  assert(msat_proof_is_term(msat_proof_get_child(p, 0)));
  msat_term a = msat_proof_get_term(msat_proof_get_child(p, 0));
  assert(msat_proof_is_term(msat_proof_get_child(p, 2)));
  msat_term b = msat_proof_get_term(msat_proof_get_child(p, 2));

  // Get the terms of the sub-proofs
  msat_term l1_term = process(msat_proof_get_child(p, 1));
  if (MSAT_ERROR_TERM(l1_term)) { return l1_term; }
  msat_term l2_term = process(msat_proof_get_child(p, 3));
  if (MSAT_ERROR_TERM(l2_term)) { return l2_term; }

  TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: la_comb: [" << a << ", " << l1_term << ", " << b << ", " << l2_term << std::endl;

  // Multiply
  msat_term a_l1_term = msat_make_times(d_env, a, l1_term);
  msat_term b_l2_term = msat_make_times(d_env, b, l2_term);

  // Add
  msat_term result = msat_make_plus(d_env, a_l1_term, b_l2_term);

  return result;
}

msat_term external_interpolator::process_la_hyp(msat_proof hyp) {
  assert(msat_proof_get_arity(hyp) == 1);
  assert(msat_proof_is_term(msat_proof_get_child(hyp, 0)));

  // Hypothesis inequality (l)
  // => Just keep if A part (remember if it's strict)

  msat_term l = msat_proof_get_term(msat_proof_get_child(hyp, 0));
  TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: la_hyp: [" << l << "]" << std::endl;
  bool l_is_negated = false;
  if (msat_term_is_not(d_env, l)) {
    l = msat_term_get_arg(l, 0);
    l_is_negated = true;
  }
  assert(msat_term_is_leq(d_env, l));

  if (d_A_atoms.count(l) == 0) {
    // B hypothesis, just 0
    return d_zero;
  }

  msat_term result;
  if (l_is_negated) {
    d_result_is_strict_inquality = true;
    result = msat_make_plus(d_env,
        msat_make_times(d_env, d_none, msat_term_get_arg(l, 0)),
        msat_make_times(d_env, d_one, msat_term_get_arg(l, 1)));
  } else {
    result = msat_make_plus(d_env,
        msat_make_times(d_env, d_one, msat_term_get_arg(l, 0)),
        msat_make_times(d_env, d_none, msat_term_get_arg(l, 1)));
  }

  return result;
}

msat_term external_interpolator::process_la_hyp_eq(msat_proof p) {

  assert(msat_proof_get_arity(p) == 2);
  assert(msat_proof_is_term(msat_proof_get_child(p, 0)));
  assert(msat_proof_is_term(msat_proof_get_child(p, 1)));

  // Hypothesis equality: just an equality
  // if first child = 1, then rhs - lhs
  // if first child = -1, then lhs - rhs

  msat_term l = msat_proof_get_term(msat_proof_get_child(p, 1));
  assert(msat_term_is_equal(d_env, l));
  if (d_A_atoms.count(l) == 0) {
    // B literals always to 0
    return d_zero;
  }

  // the first child is always either -1 or 1, and denotes which side of
  // the equality needs to be considered
  msat_term side = msat_proof_get_term(msat_proof_get_child(p, 0));
  bool neg = false;

  TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: la_hyp_eq: [" << side << ", " << l << "]" << std::endl;

  if (msat_term_id(side) == msat_term_id(d_one)) {
    neg = true;
  } else {
    assert(msat_term_id(side) == msat_term_id(d_none));
  }

  msat_term result;
  if (neg) {
    result = msat_make_plus(d_env,
        msat_make_times(d_env, d_none, msat_term_get_arg(l, 0)),
        msat_make_times(d_env, d_one, msat_term_get_arg(l, 1)));
  } else {
    result = msat_make_plus(d_env,
        msat_make_times(d_env, d_one, msat_term_get_arg(l, 0)),
        msat_make_times(d_env, d_none, msat_term_get_arg(l, 1)));
  }

  return result;
}

}
}


#endif
