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
#include "utils/exception.h"

#include <cassert>
#include <string>
#include <iostream>

namespace sally {
namespace smt {

external_interpolator::external_interpolator(size_t instance, msat_env env, std::string interpolation_type, std::string apron_domain)
: d_interpolation_type(INT_STANDARD)
, d_instance(instance)
, d_env(env)
, d_result_is_strict_inquality(false)
, d_frame(0)
{
  d_zero = msat_make_number(env, "0");
  d_one = msat_make_number(env, "1");
  d_none = msat_make_number(env, "-1");

  if (interpolation_type == "standard") {
    d_interpolation_type = INT_STANDARD;
  } else if (interpolation_type == "conflict-resolution") {
    d_interpolation_type = INT_CONFLICT_RESOLUTION;
  } else if (interpolation_type == "conflict-resolution-ai") {
    d_interpolation_type = INT_CONFLICT_RESOLUTION_AI;
  } else {
    throw exception("Unknown intepolation type");
  }

  if (apron_domain == "polka") {
    d_apron_domain = conflict_resolution::DOMAIN_POLKA;
  } else if (apron_domain == "oct") {
    d_apron_domain = conflict_resolution::DOMAIN_OCT;
  } else if (apron_domain == "box") {
    d_apron_domain = conflict_resolution::DOMAIN_BOX;
  } else {
    throw exception("Unknown domain type");
  }
}

void external_interpolator::print(std::ostream& out, msat_proof p, std::string indent) const {
  out << indent;
  if (msat_proof_is_term(p)) {
    out << msat_proof_get_term(p);
  } else {
    out << "(" << msat_proof_get_name(p) << std::endl;
    for (size_t i = 0; i < msat_proof_get_arity(p); ++i) {
      print(out, msat_proof_get_child(p, i), indent + "  ");
      out << std::endl;
    }
    out << indent;
    out << ")";
  }
  if (indent == "") {
    out << std::endl;
  }
}

msat_term external_interpolator::compute(msat_term *a, msat_term *b, msat_proof p) {

  TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: computing interpolant." << std::endl;

  size_t i;

  msat_term result;
  MSAT_MAKE_ERROR_TERM(result);

  if (output::trace_tag_is_enabled("mathsat5::extitp")) {
    std::ostream& trace = output::get_trace_stream();
    for (i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
      msat_term l = a[i];
      char* str = msat_term_repr(l);
      trace << "mathsat5[" << d_instance << "]: a[" << i << "]:" << str << std::endl;
      msat_free(str);
    }
    for (i = 0; !MSAT_ERROR_TERM(b[i]); ++ i) {
      msat_term l = b[i];
      char* str = msat_term_repr(l);
      trace << "mathsat5[" << d_instance << "]: b[" << i << "]:" << str << std::endl;
      msat_free(str);
    }
    print(trace, p, "");
  }

  switch (d_interpolation_type) {
  case INT_STANDARD: {
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
      result = msat_make_not(d_env, msat_make_leq(d_env, d_zero, interpolant_term));
    } else {
      result = msat_make_leq(d_env, interpolant_term, d_zero);
    }

    if (output::trace_tag_is_enabled("mathsat5::extitp")) {
      char* str = msat_term_repr(result);
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: standard interpolant: " << str << std::endl;
      msat_free(str);
    }
    break;
  }
  case INT_CONFLICT_RESOLUTION_AI:
  case INT_CONFLICT_RESOLUTION: {
    // Do conflict resolution
    if (can_handle(p)) {
      conflict_resolution cr(d_env);
      cr.set_var_to_var_map(&d_variables_AB);
      if (d_interpolation_type == INT_CONFLICT_RESOLUTION_AI) {
        bool use_widening = false; // d_frame >= 5;
        cr.set_use_apron(true, d_apron_domain, use_widening);
      }
      cr.set_collection_type(conflict_resolution::COLLECT_TOP);
      result = cr.interpolate(a, b);
    } else {
      if (output::trace_tag_is_enabled("mathsat5::extitp::unhandled")) {
        std::ostream& trace = output::get_trace_stream();
        print(trace, p, "");
      }
    }
    break;
  }
  default:
    assert(false);
  }

  if (output::trace_tag_is_enabled("mathsat5::extitp")) {
    if (!MSAT_ERROR_TERM(result)) {
      char* str = msat_term_repr(result);
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: final interpolant: " << str << std::endl;
      msat_free(str);
    } else {
      TRACE("mathsat5::extitp") << "mathsat5[" << d_instance << "]: can't handle" << std::endl;
    }
  }

  return result;
}

bool external_interpolator::can_handle(msat_proof p) {
  std::string name = msat_proof_get_name(p);
  if (name == "la-comb") {
     return true;
   } else if (name == "la-hyp") {
     return true;
   } else if (name == "la-hyp-eq") {
     return true;
   } else {
     return false;
   }
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

void external_interpolator::add_var_pair(msat_term x, msat_term x_next) {
  assert(d_variables_AB.find(x) == d_variables_AB.end());
  d_variables_AB[x] = x_next;
}

void external_interpolator::set_frame(size_t frame) {
  d_frame = frame;
}

void external_interpolator::interpolation_begin() {
  d_interpolation_count ++;
}

}
}


#endif
