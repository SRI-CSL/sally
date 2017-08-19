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

#include <iostream>

#include "conflict_resolution.h"
#include "utils/trace.h"

namespace sally {
namespace smt {

std::ostream& operator << (std::ostream& out, msat_term t) {
  msat_term l = t;
  char* str = msat_term_repr(l);
  out << str;
  msat_free(str);
  return out;
}

std::ostream& operator << (std::ostream& out, const conflict_resolution::constraint& C) {
  C.to_stream(out);
  return out;
}

conflict_resolution::conflict_resolution(msat_env env)
: d_env(env)
{
}

conflict_resolution::bound_info::bound_info()
: d_is_strict(true)
, d_is_infinity(true)
{}

conflict_resolution::variable_info::variable_info()
: d_source(VARIABLE_A)
{
  MSAT_MAKE_ERROR_TERM(d_x);
}

conflict_resolution::variable_info::variable_info(msat_term x, variable_source source)
: d_source(source)
, d_x(x)
{
}

void conflict_resolution::variable_info::set_source(variable_source source) {
  if (source != d_source) {
    d_source = VARIABLE_B;
  }
}

conflict_resolution::variable_source conflict_resolution::variable_info::get_source() const {
  return d_source;
}

msat_term conflict_resolution::variable_info::get_msat_term() const {
  return d_x;
}

conflict_resolution::constraint::constraint()
: type(CONSTRAINT_LE)
{
}

void conflict_resolution::constraint::to_stream(std::ostream& out) const {
  out << "(";
  for (size_t i = 0; i < a.size(); ++ i) {
    if (i) out << " ";
    out << a[i] << "*" << "x" << x[i];
  }
  if (b.sgn()) {
    out << " " << b;
  }
  switch (type) {
  case CONSTRAINT_LE:
    out << " <= 0";
    break;
  case CONSTRAINT_LT:
    out << " < 0";
    break;
  case CONSTRAINT_EQ:
    out << " = 0";
    break;
  default:
    assert(false);
  }
  out << ")";
}

conflict_resolution::variable_id conflict_resolution::add_variable(msat_term t, variable_source source) {

  // Check if the variable is already there
  term_to_variable_id_map::const_iterator find = d_term_to_variable_id_map.find(t);
  if (find != d_term_to_variable_id_map.end()) {
    // Change the class if different
    variable_id t_id = find->second;
    d_variable_info[t_id].set_source(source);
    return t_id;
  }

  // New variable, add it
  variable_id t_id = d_variable_info.size();
  d_variable_info.push_back(variable_info(t, source));
  d_term_to_variable_id_map[t] = t_id;

  return t_id;
}

conflict_resolution::constraint_id conflict_resolution::add_constraint(msat_term t, constraint_source source) {

  // Check if the constraint is already there
  term_to_constraint_id_map::const_iterator find = d_term_to_constraint_id_map.find(t);
  if (find != d_term_to_constraint_id_map.end()) {
    // Existing constraint might be from A, and we get the same from B.
    // This doesn't affect unsatisfiability, so we just ignore it
    return find->second;
  }

  // Create the new constraints
  constraint_id t_id = d_constraints.size();
  d_constraints.push_back(constraint());
  constraint C = d_constraints.back();

  // Is the constraint negated
  bool negated = msat_term_is_not(d_env, t);
  if (negated) { t = msat_term_get_arg(t, 0); }

  // Setup the constraint
  assert(msat_term_is_equal(d_env, t) || msat_term_is_leq(d_env, t));
  C.type = msat_term_is_equal(d_env, t) ? CONSTRAINT_EQ : CONSTRAINT_LE;

  // Add the term
  msat_term lhs = msat_term_get_arg(t, 0);
  msat_term rhs = msat_term_get_arg(t, 1);
  add_to_constraint(C, expr::rational(1, 1), lhs, source);
  add_to_constraint(C, expr::rational(-1, 1), rhs, source);

  TRACE("mathsat5::cr") << "CR: added constraint: " << C << std::endl;

  return t_id;
}

void conflict_resolution::add_to_constraint(constraint& C, const expr::rational& a, msat_term t, conflict_resolution::constraint_source source) {

  if (msat_term_is_constant(d_env, t)) {
    // Variables
    variable_id x = variable_null;
    switch (source) {
    case CONSTRAINT_A:
      x = add_variable(t, VARIABLE_A);
      break;
    case CONSTRAINT_B:
      x = add_variable(t, VARIABLE_B);
      break;
    default:
      assert(false);
    }
    C.a.push_back(a);
    C.x.push_back(x);
  } else if (msat_term_is_plus(d_env, t)) {
    size_t size = msat_term_arity(t);
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      add_to_constraint(C, a, child, source);
    }
  } else if (msat_term_is_times(d_env, t)) {
    assert(msat_term_arity(t) == 2);
    assert(false);
  } else if (msat_term_is_number(d_env, t)) {
    // Constants
    mpq_t constant;
    mpq_init(constant);
    msat_term_to_number(d_env, t, constant);
    C.b += expr::rational(constant);
    mpq_clear(constant);
  } else {
    assert(false);
  }
}

bool conflict_resolution::variable_cmp::operator () (variable_id x, variable_id y) const {
  // Sort the variables so that B < A, otherwise by mathsat id
  variable_source x_source = cr.d_variable_info[x].get_source();
  variable_source y_source = cr.d_variable_info[y].get_source();

  // If different sources, then sort as B < A (as in enum)
  if (x_source != y_source) {
    return x_source < y_source;
  }

  // Same source, sort by mathsat id
  msat_term x_term = cr.d_variable_info[x].get_msat_term();
  msat_term y_term = cr.d_variable_info[y].get_msat_term();
  return msat_term_id(x_term) < msat_term_id(y_term);
}

/** Interpolate between the constraints in a and the constraint b */
msat_term conflict_resolution::interpolate(msat_term* a, msat_term b) {

  TRACE("mathsat5::cr") << "CR: computing interpolant." << std::endl;

  // A: Add all the constraints
  for (size_t i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
    TRACE("mathsat5::cr") << "CR: a[" << i << "]:" << a[i] << std::endl;
    if (!msat_term_is_equal(d_env, a[i]) && !msat_term_is_leq(d_env, a[i])) {
      return b;
    }
    add_constraint(a[i], CONSTRAINT_A);
  }
  TRACE("mathsat5::cr") << "CR: b:" << b << std::endl;
  if (!msat_term_is_equal(d_env, b) && !msat_term_is_leq(d_env, b)) {
    return b;
  }
  add_constraint(b, CONSTRAINT_B);

  // B: Order the variables B -> AB -> A
  std::vector<variable_id> all_vars;
  for (variable_id x = 0; x < d_variable_info.size(); ++ x) {
    all_vars.push_back(x);
  }
  variable_cmp cmp(*this);
  std::sort(all_vars.begin(), all_vars.end(), cmp);

  return b;
}

}
}

#endif
