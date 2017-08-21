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
#include <algorithm>

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

std::ostream& operator << (std::ostream& out, const conflict_resolution::variable_info& info) {
  info.to_stream(out);
  return out;
}

std::ostream& operator << (std::ostream& out, const conflict_resolution::linear_term& info) {
  info.to_stream(out);
  return out;
}

conflict_resolution::conflict_resolution(msat_env env)
: d_env(env)
{
}

conflict_resolution::bound_info::bound_info()
: d_is_strict(true)
, d_is_infinity(true)
, d_constraint(constraint_null)
{}

void conflict_resolution::bound_info::clear() {
  d_bound = expr::rational();
  d_is_strict = true;
  d_is_infinity = true;
  d_constraint = constraint_null;
}

bool conflict_resolution::bound_info::is_infinity() const {
  return d_is_infinity;
}

bool conflict_resolution::bound_info::is_strict() const {
  return d_is_strict;
}

const expr::rational conflict_resolution::bound_info::get_bound() const {
  assert(!d_is_infinity);
  return d_bound;
}

conflict_resolution::constraint_id conflict_resolution::bound_info::get_constraint() const {
  assert(!d_is_infinity);
  return d_constraint;
}

void conflict_resolution::bound_info::set(const expr::rational& bound, bool is_strict, constraint_id C_id) {
  d_bound = bound;
  d_is_infinity = false;
  d_is_strict = is_strict;
  d_constraint = C_id;
}

bool conflict_resolution::bound_info::consistent(const bound_info& lb, const bound_info& ub) {
  // Any infinity is consistent
  if (lb.is_infinity() || ub.is_infinity()) {
    return true;
  }
  // We have both bounds, check if they are consistent
  if (lb.is_strict() || ub.is_strict()) {
    return (lb.get_bound() < ub.get_bound());
  } else {
    // Both are leq
    return (lb.get_bound() <= ub.get_bound());
  }
}

conflict_resolution::variable_info::variable_info()
: d_source(VARIABLE_A)
{
  MSAT_MAKE_ERROR_TERM(d_msat_term);
}

conflict_resolution::variable_info::variable_info(msat_term x, variable_source source)
: d_source(source)
, d_msat_term(x)
{
}

void conflict_resolution::variable_info::clear_bounds() {
  d_lb.clear();
  d_ub.clear();
}

void conflict_resolution::variable_info::add_source(variable_source source) {
  if (source != d_source) {
    d_source = VARIABLE_B;
  }
}

conflict_resolution::variable_source conflict_resolution::variable_info::get_source() const {
  return d_source;
}

msat_term conflict_resolution::variable_info::get_msat_term() const {
  return d_msat_term;
}

const expr::rational conflict_resolution::variable_info::get_value() const {
  return d_value;
}

conflict_resolution::constraint_id conflict_resolution::variable_info::get_lb_constraint() const {
  return d_lb.get_constraint();
}

conflict_resolution::constraint_id conflict_resolution::variable_info::get_ub_constraint() const {
  return d_ub.get_constraint();
}

bool conflict_resolution::variable_info::set_lower_bound(const expr::rational& bound, bool is_strict, constraint_id C_id) {

  if (d_lb.is_infinity()) {
    // We always improve on infinity
    d_lb.set(bound, is_strict, C_id);
  } else {
    int cmp = bound.cmp(d_lb.get_bound());
    if (cmp == 0) {
      // Only improve if old was not strict and new one is
      if (!d_lb.is_strict() && is_strict) {
        d_lb.set(bound, is_strict, C_id);
      }
    } else if (cmp < 0) {
      // New bound is smaller, nothing to do
    } else if (cmp > 0) {
      // New bound is larger, definitely improve
      d_lb.set(bound, is_strict, C_id);
    }
  }

  return bound_info::consistent(d_lb, d_ub);
}

bool conflict_resolution::variable_info::set_upper_bound(const expr::rational& bound, bool is_strict, constraint_id C_id) {

  if (d_ub.is_infinity()) {
    // We always improve on infinity
    d_ub.set(bound, is_strict, C_id);
  } else {
    int cmp = bound.cmp(d_ub.get_bound());
    if (cmp == 0) {
      // Only improve if old was not strict and new one is
      if (!d_ub.is_strict() && is_strict) {
        d_ub.set(bound, is_strict, C_id);
      }
    } else if (cmp < 0) {
      // New bound is smaller, definitely improve
      d_ub.set(bound, is_strict, C_id);
    } else {
      // New bound is larger, nothing to do
    }
  }

  return bound_info::consistent(d_lb, d_ub);
}

bool conflict_resolution::variable_info::pick_value() {

  if (!bound_info::consistent(d_lb, d_ub)) {
    return false;
  }

  // (-inf, +inf)
  if (d_lb.is_infinity() && d_ub.is_infinity()) {
    d_value = expr::rational(0, 1); // x -> 0
  } else
  // (-inf, ub)
  if (d_lb.is_infinity()) {
    d_value = d_ub.get_bound() - 1; // x -> ub - 1
  } else
  // (lb, +inf)
  if (d_ub.is_infinity()) {
    d_value = d_lb.get_bound() + 1; // x -> lb + 1
  }
  // All ok, pick the mid-point
  else {
    d_value = (d_lb.get_bound() + d_ub.get_bound()) / 2;
  }

  return true;
}

void conflict_resolution::variable_info::to_stream(std::ostream& out) const {
  out << "[";
  out << d_msat_term;
  out << " in ";
  if (d_lb.is_strict()) { out << "("; }
  else { out << "["; }
  if (d_lb.is_infinity()) { out << "-inf"; }
  else { out << d_lb.get_bound(); }
  out << ", ";
  if (d_ub.is_infinity()) { out << "+inf"; }
  else { out << d_ub.get_bound(); }
  if (d_ub.is_strict()) { out << ")"; }
  else { out << "]"; }
  out << ", v = " << d_value;
  out << "]";
}

conflict_resolution::constraint::constraint()
: d_op(CONSTRAINT_EQ)
{
}

conflict_resolution::constraint::constraint(const linear_term& t, constraint_op type)
: d_op(type)
, d_b(t.get_constant())
{
  // Copy over the linear term
  const var_to_rational_map& ax = t.get_monomials();
  for (var_to_rational_map::const_iterator it = ax.begin(); it != ax.end(); ++ it) {
    if (it->second.sgn()) {
      d_ax.push_back(monomial(it->second, it->first));
    }
  }
}

conflict_resolution::constraint::constraint(const linear_term& t, constraint_op type, const monomial_cmp& cmp)
: d_op(type)
, d_b(t.get_constant())
{
  // Copy over the linear term
  const var_to_rational_map& ax = t.get_monomials();
  for (var_to_rational_map::const_iterator it = ax.begin(); it != ax.end(); ++ it) {
    if (it->second.sgn()) {
      d_ax.push_back(monomial(it->second, it->first));
    }
  }
  if (d_ax.size() > 0) {
    std::vector<monomial>::iterator max_it = std::max_element(d_ax.begin(), d_ax.end(), cmp);
    std::iter_swap(d_ax.begin(), max_it);
  }
}

void conflict_resolution::constraint::setup_top_variable(const monomial_cmp& cmp) {
  if (d_ax.size() > 0) {
    std::vector<monomial>::iterator max_it = std::max_element(d_ax.begin(), d_ax.end(), cmp);
    std::iter_swap(d_ax.begin(), max_it);
  }
}

conflict_resolution::linear_term::linear_term(const constraint& C)
: d_b(C.get_constant())
{
  const monomial_list monomials = C.get_monomials();
  monomial_list::const_iterator it = monomials.begin();
  for (; it != monomials.end(); ++ it) {
    const monomial& m = *it;
    d_ax[m.x] += m.a;
  }
}

void conflict_resolution::linear_term::add(const expr::rational& a, const linear_term& t) {
  assert(this != &t);
  d_b += a*t.d_b;
  var_to_rational_map::const_iterator t_it = t.d_ax.begin();
  for(; t_it != t.d_ax.end(); ++ t_it) {
    d_ax[t_it->first] += a*t_it->second;
  }
}

void conflict_resolution::linear_term::add(const expr::rational& a, variable_id x) {
  d_ax[x] += a;
}

void conflict_resolution::linear_term::add(const expr::rational& a) {
  d_b += a;
}

const conflict_resolution::var_to_rational_map& conflict_resolution::linear_term::get_monomials() const {
  return d_ax;
}

const expr::rational& conflict_resolution::linear_term::get_constant() const {
  return d_b;
}

void conflict_resolution::linear_term::to_stream(std::ostream& out) const {
  var_to_rational_map::const_iterator it = d_ax.begin();
  for (; it != d_ax.end(); ++ it) {
    out << it->second << "*" << "x" << it->first << " + ";
  }
  out << d_b;
}

void conflict_resolution::constraint::negate() {
  // !(t < 0) = (t >= 0) = (-t <= 0)
  // !(t <= 0) = (t > 0) = (-t < 0)
  // We don't negate equalities

  // Negate coefficients
  for (size_t i = 0; i < d_ax.size(); ++ i) {
    d_ax[i].a = d_ax[i].a.negate();
  }
  d_b = d_b.negate();

  // Negate the type
  switch (d_op) {
  case CONSTRAINT_EQ:
    assert(false);
    break;
  case CONSTRAINT_LT:
    d_op = CONSTRAINT_LE;
    break;
  case CONSTRAINT_LE:
    d_op = CONSTRAINT_LT;
    break;
  default:
    assert(false);
  }
}

size_t conflict_resolution::constraint::size() const {
  return d_ax.size();
}

conflict_resolution::variable_id conflict_resolution::constraint::get_top_variable() const {
  assert(d_ax.size() > 0);
  return d_ax[0].x;
}

const expr::rational& conflict_resolution::constraint::get_top_coefficient() const {
  assert(d_ax.size() > 0);
  return d_ax[0].a;
}

const conflict_resolution::monomial_list& conflict_resolution::constraint::get_monomials() const {
  return d_ax;
}

const expr::rational& conflict_resolution::constraint::get_constant() const {
  return d_b;
}

void conflict_resolution::constraint::swap(constraint& C) {
  std::swap(d_op, C.d_op);
  std::swap(d_b, C.d_b);
  d_ax.swap(C.d_ax);
}

conflict_resolution::constraint_op conflict_resolution::constraint::get_op() const {
  return d_op;
}

void conflict_resolution::constraint::to_stream(std::ostream& out) const {
  out << "(";
  for (size_t i = 0; i < d_ax.size(); ++ i) {
    if (i) out << " + ";
    out << d_ax[i].a << "*" << "x" << d_ax[i].x;
  }
  if (d_ax.size() == 0) {
    out << d_b;
  } else if (d_b.sgn()) {
    out << " + " << d_b;
  }
  switch (d_op) {
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
    d_variable_info[t_id].add_source(source);
    return t_id;
  }

  // New variable, add it
  variable_id t_id = d_variable_info.size();
  d_variable_info.push_back(variable_info(t, source));
  d_term_to_variable_id_map[t] = t_id;
  d_top_var_to_constraint.push_back(constraint_list());
  assert(d_variable_info.size() == d_top_var_to_constraint.size());

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

  // Is the constraint negated
  bool is_not = false;
  while (msat_term_is_not(d_env, t)) {
    is_not = !is_not;
    t = msat_term_get_arg(t, 0);
  }

  // Setup the constraint
  assert(msat_term_is_equal(d_env, t) || msat_term_is_leq(d_env, t));
  constraint_op type = msat_term_is_equal(d_env, t) ? CONSTRAINT_EQ : CONSTRAINT_LE;

  // Add the terms
  linear_term constraint_term;
  msat_term lhs = msat_term_get_arg(t, 0);
  msat_term rhs = msat_term_get_arg(t, 1);
  add_to_linear_term(constraint_term, expr::rational(1, 1), lhs, source);
  add_to_linear_term(constraint_term, expr::rational(-1, 1), rhs, source);

  // Create the constraint
  constraint_id t_id = d_constraints.size();
  d_constraints.push_back(constraint(constraint_term, type));
  constraint& C = d_constraints.back();

  // Negate if necessary
  if (is_not) {
    C.negate();
  }

  TRACE("mathsat5::cr") << "CR: added constraint: " << C << std::endl;

  return t_id;
}

void conflict_resolution::add_to_linear_term(linear_term& term, const expr::rational& a, msat_term t, conflict_resolution::constraint_source source) {

  if (msat_term_is_constant(d_env, t) || msat_term_is_term_ite(d_env, t)) {
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
    term.add(a, x);
  } else if (msat_term_is_plus(d_env, t)) {
    size_t size = msat_term_arity(t);
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      add_to_linear_term(term, a, child, source);
    }
  } else if (msat_term_is_times(d_env, t)) {
    assert(msat_term_arity(t) == 2);
    msat_term child0 = msat_term_get_arg(t, 0);
    msat_term child1 = msat_term_get_arg(t, 1);
    if (!msat_term_is_number(d_env, child0)) {
      assert(msat_term_is_number(d_env, child1));
      std::swap(child0, child1);
    }
    // Get the constant
    mpq_t constant;
    mpq_init(constant);
    msat_term_to_number(d_env, child0, constant);
    expr::rational new_a = a*expr::rational(constant);
    mpq_clear(constant);
    // Add second child to the constraint
    add_to_linear_term(term, new_a, child1, source);
  } else if (msat_term_is_number(d_env, t)) {
    // Constants
    mpq_t constant;
    mpq_init(constant);
    msat_term_to_number(d_env, t, constant);
    term.add(a*expr::rational(constant));
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

bool conflict_resolution::monomial_cmp::operator () (const monomial& ax, const monomial& by) const {
  // Sort the variables so that B < A, otherwise by mathsat id
  variable_source x_source = cr.d_variable_info[ax.x].get_source();
  variable_source y_source = cr.d_variable_info[by.x].get_source();

  // If different sources, then sort as B < A (as in enum)
  if (x_source != y_source) {
    return x_source < y_source;
  }

  // Same source, sort by mathsat id
  msat_term x_term = cr.d_variable_info[ax.x].get_msat_term();
  msat_term y_term = cr.d_variable_info[by.x].get_msat_term();
  size_t x_term_id = msat_term_id(x_term);
  size_t y_term_id = msat_term_id(y_term);
  if (x_term_id != y_term_id) {
    return  x_term_id < y_term_id;
  }

  // Otherwise compare the constants (shouldn't really happen)
  return ax.a < by.a;
}

bool conflict_resolution::can_interpolate(msat_term t) const {
  bool is_not = false;
  while (msat_term_is_not(d_env, t)) {
    is_not = !is_not;
    t = msat_term_get_arg(t, 0);
  }
  if (msat_term_is_leq(d_env, t)) {
    return true;
  }
  if (!is_not && msat_term_is_equal(d_env, t)) {
    return true;
  }
  return false;
}

msat_term conflict_resolution::interpolate(msat_term* a, msat_term b) {

  TRACE("mathsat5::cr") << "CR: computing interpolant." << std::endl;

  // All A constraints
  constraint_set A_constraints;
  // The b constraint
  constraint_id b_id;

  // A: Add all the constraints
  for (size_t i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
    TRACE("mathsat5::cr") << "CR: a[" << i << "]:" << a[i] << std::endl;
    if (!can_interpolate(a[i])) {
      return msat_make_not(d_env, b);
    }
    constraint_id c_id = add_constraint(a[i], CONSTRAINT_A);
    A_constraints.insert(c_id);
  }
  TRACE("mathsat5::cr") << "CR: b:" << b << std::endl;
  if (!can_interpolate(b)) {
    return msat_make_not(d_env, b);
  }
  b_id = add_constraint(b, CONSTRAINT_B);

  // B: Order the variables B -> AB -> A
  variable_cmp var_cmp(*this);
  std::vector<variable_id> all_vars;
  for (variable_id x = 0; x < d_variable_info.size(); ++ x) {
    all_vars.push_back(x);
  }
  std::sort(all_vars.begin(), all_vars.end(), var_cmp);

  // Setup the constraints: setup_top_variable variables
  monomial_cmp mon_cmp(*this);
  constraint_set::const_iterator it = A_constraints.begin();
  for (; it != A_constraints.end(); ++ it) {
    constraint_id C_id = *it;
    constraint& C = d_constraints[C_id];
    C.setup_top_variable(mon_cmp);
    d_top_var_to_constraint[C.get_top_variable()].push_back(C_id);
  }
  constraint& C_b = d_constraints[b_id];
  C_b.setup_top_variable(mon_cmp);
  d_top_var_to_constraint[C_b.get_top_variable()].push_back(b_id);

  if (output::trace_tag_is_enabled("mathsat5::cr")) {
    TRACE("mathsat5::cr") << "CR: variable_order:" << std::endl;
    for (size_t i = 0; i < all_vars.size(); ++ i) {
      TRACE("mathsat5::cr") << "- x" << all_vars[i];
      TRACE("mathsat5::cr") << " (" << (d_variable_info[all_vars[i]].get_source() == VARIABLE_A ? "A" : "B") << "):";
      const constraint_list& x_cstrs = d_top_var_to_constraint[all_vars[i]];
      for (size_t j = 0; j < x_cstrs.size(); ++ j) {
        TRACE("mathsat5::cr") << " " << d_constraints[x_cstrs[j]];
      }
      TRACE("mathsat5::cr") << std::endl;
    }
  }

  // Set of interpolants we will collect
  constraint_set interpolants;

  // Conflict resolution: try to assign all the variables
  bool ok = true;
  for (size_t k = 0; k < all_vars.size(); ++ k) {

    if (output::trace_tag_is_enabled("mathsat5::cr")) {
      TRACE("mathsat5::cr") << "CR: current assignement (" << k << "):" << std::endl;
      for (size_t i = 0; i < k; ++ i) {
        TRACE("mathsat5::cr") << "- x" << all_vars[i] << " -> " << d_variable_info[all_vars[i]].get_value() << std::endl;
      }
    }

    // Variable we're assigning
    variable_id x = all_vars[k];
    variable_source x_source = d_variable_info[x].get_source();
    TRACE("mathsat5::cr") << "CR: propagating on x" << x << ": " << d_variable_info[x] << std::endl;

    // All the constraints where x is the top variable
    const constraint_list& x_constraints = d_top_var_to_constraint[x];
    constraint_list::const_iterator it = x_constraints.begin();
    for (; ok && it != x_constraints.end(); ++ it) {
      // Propagate new bound if implied by this constraint  
      constraint_id C_id = *it;
      assert(d_constraints[C_id].get_top_variable() == x);
      ok = propagate(C_id);
      TRACE("mathsat5::cr") << "CR: propagation: " << d_variable_info[x] << std::endl;
    }

    while (!ok) {

      // Create the resolvent constraint (this is first due to resizing)
      constraint_id R_id = d_constraints.size();
      d_constraints.push_back(constraint());
      constraint& R = d_constraints.back();

      // Get the constraints to resolve
      constraint_id lb_C_id = d_variable_info[x].get_lb_constraint();
      constraint_id ub_C_id = d_variable_info[x].get_ub_constraint();
      const constraint& lb_C = d_constraints[lb_C_id];
      const constraint& ub_C = d_constraints[ub_C_id];

      // Any A premises in B variables are added to interpolant (needed for deduction)
      if (x_source == VARIABLE_B) {
        // We add any premises from A
        if (A_constraints.count(ub_C_id) > 0) {
          TRACE("mathsat5::cr") << "CR: adding to interpolant: " << ub_C << std::endl;
          interpolants.insert(ub_C_id);
        }
        if (A_constraints.count(lb_C_id) > 0) {
          TRACE("mathsat5::cr") << "CR: adding to interpolant: " << lb_C << std::endl;
          interpolants.insert(lb_C_id);
        }
      }

      TRACE("mathsat5::cr") << "CR: resolving:" << "C_lb: " << lb_C << std::endl;
      TRACE("mathsat5::cr") << "CR: resolving:" << "C_ub: " << ub_C << std::endl;

      // Now resolve the constraints
      resolve(lb_C, ub_C, R);
      assert(!evaluate(R));
      TRACE("mathsat5::cr") << "CR: resolvent:" << "R: " << R << std::endl;

      // If resolvent is empty, we're done
      if (R.size() == 0) {
        return construct_msat_term(interpolants);
      } else {

        // Check if to add to the interpolant
        variable_id x_new = R.get_top_variable();
        variable_id x_new_source = d_variable_info[x_new].get_source();

        if (x_source != x_new_source) {
          // Learning into B for the first time -> add to interpolant
          assert(x_source == VARIABLE_A && x_new_source == VARIABLE_B);
          TRACE("mathsat5::cr") << "CR: adding to interpolant: " << R << std::endl;
          interpolants.insert(R_id);
        }

        // Backtrack to the new top variable
        x = x_new;
        x_source = d_variable_info[x].get_source();
        while (all_vars[k] != x) {
          d_variable_info[all_vars[k]].clear_bounds();
          k --;
        }

        // Add the constraint to list of x
        d_top_var_to_constraint[x].push_back(R_id);
      }

      // Propagate the new constraint
      ok = propagate(R_id);
      TRACE("mathsat5::cr") << "CR: propagation: " << d_variable_info[x] << std::endl;
    }

    // We're done resolving, we can now pick a value
    ok = d_variable_info[x].pick_value();
    assert(ok);
  }

  assert(false);
  return b;
}

bool conflict_resolution::propagate(constraint_id C_id) {

  bool ok = true; // No conflicts yet

  constraint& C = d_constraints[C_id];
  const monomial_list monomials = C.get_monomials();

  TRACE("mathsat5::cr") << "CR: propagating on: " << C << std::endl;

  // C = a*x + R ? 0
  variable_id x = monomials[0].x;
  const expr::rational& a = monomials[0].a;

  TRACE("mathsat5::cr") << "CR: current " << d_variable_info[x] << std::endl;

  // Calculate the sum of the rest of the constraint
  expr::rational R;
  for (size_t i = 1; i < monomials.size(); ++ i) {
    const monomial& m = monomials[i];
    R += m.a * d_variable_info[m.x].get_value();
  }
  R += C.get_constant();

  // The value of the bound
  expr::rational bound = -R / a;

  // The variable info
  variable_info& var_info = d_variable_info[x];

  switch (C.get_op()) {
  case CONSTRAINT_LE:
    // a*x + r <= 0
    if (a.sgn() > 0) {
      // x <= bound
      ok = ok && var_info.set_upper_bound(bound, false, C_id);
    } else {
      // x >= bound
      ok = ok && var_info.set_lower_bound(bound, false, C_id);
    }
    break;
  case CONSTRAINT_LT:
    // a*x + r < 0
    if (a.sgn() > 0) {
      // x < bound
      ok = ok && var_info.set_upper_bound(bound, true, C_id);
    } else {
      // x > bound
      ok = ok && var_info.set_lower_bound(bound, true, C_id);
    }
    break;
  case CONSTRAINT_EQ:
    // a*x + r = 0 => x = bound
    ok = ok && var_info.set_lower_bound(bound, false, C_id);
    ok = ok && var_info.set_upper_bound(bound, false, C_id);
    break;
  }

  return ok;
}

msat_term conflict_resolution::construct_msat_term(const constraint& C) {

  msat_term zero = msat_make_number(d_env, "0");

  msat_term result = msat_make_number(d_env, C.get_constant().mpq().get_str().c_str());
  const monomial_list& monomials = C.get_monomials();
  for (size_t i = 0; i < monomials.size(); ++ i) {
    const monomial& m = monomials[i];
    msat_term a = msat_make_number(d_env, m.a.mpq().get_str().c_str());
    msat_term x = d_variable_info[m.x].get_msat_term();
    msat_term ax = msat_make_times(d_env, a, x);
    result = msat_make_plus(d_env, result, ax);
  }

  switch (C.get_op()) {
  case CONSTRAINT_EQ:
    result = msat_make_equal(d_env, result, zero);
    break;
  case CONSTRAINT_LT:
    result = msat_make_leq(d_env, zero, result);
    result = msat_make_not(d_env, result);
    break;
  case CONSTRAINT_LE:
    result = msat_make_leq(d_env, result, zero);
    break;
  default:
    assert(false);
  }

  return result;
}

msat_term conflict_resolution::construct_msat_term(const constraint_list& list) {
  if (list.size() == 0) {
    return msat_make_true(d_env);
  }
  msat_term result = construct_msat_term(d_constraints[list[0]]);
  for (size_t i = 1; i < list.size(); ++ i) {
    msat_term current = construct_msat_term(d_constraints[list[i]]);
    result = msat_make_and(d_env, result, current);
  }
  return result;
}

msat_term conflict_resolution::construct_msat_term(const constraint_set& set) {
  if (set.size() == 0) {
    return msat_make_true(d_env);
  }
  constraint_set::const_iterator it = set.begin();
  msat_term result = construct_msat_term(d_constraints[*it]);
  for (++ it; it != set.end(); ++ it) {
    msat_term current = construct_msat_term(d_constraints[*it]);
    result = msat_make_and(d_env, result, current);
  }
  return result;
}

void conflict_resolution::resolve(const constraint& C1, const constraint& C2, constraint& R) const {

  assert(C1.get_top_variable() == C2.get_top_variable());
  const expr::rational& C1_a = C1.get_top_coefficient();
  const expr::rational& C2_a = C2.get_top_coefficient();
  linear_term C1_term(C1);
  linear_term C2_term(C2);

  // If the coefficients of x are opposite signs, we use their absolute values
  // to cancel x. If they are not, we must negate one of the equality multipliers to cancel.
  bool C1_C2_opposite = C1_a.sgn()*C2_a.sgn() < 0;
  assert(C1_C2_opposite || C1.get_op() == CONSTRAINT_EQ || C2.get_op() == CONSTRAINT_EQ);
  expr::rational t1_c = C1_a.abs();
  expr::rational t2_c = C2_a.abs();
  if (!C1_C2_opposite) {
    if (C1.get_op() == CONSTRAINT_EQ) { t2_c = t2_c.negate(); }
    else { t1_c = t1_c.negate(); }
  }

  // We now compute t2_c * t1 + t1_c * t2
  linear_term R_term;
  R_term.add(t2_c, C1_term);
  TRACE("mathsat5::cr") << "CR: R_term: " << R_term << std::endl;
  R_term.add(t1_c, C2_term);
  TRACE("mathsat5::cr") << "CR: R_term: " << R_term << std::endl;

  // Finally compute the type of constraint
  constraint_op R_type = C1.get_op();
  constraint_op C2_type = C2.get_op();
  switch(C2_type) {
  case CONSTRAINT_EQ:
    break;
  case CONSTRAINT_LT:
    R_type = CONSTRAINT_LT;
    break;
  case CONSTRAINT_LE:
    if (R_type == CONSTRAINT_LT) {
      R_type = CONSTRAINT_LT;
    } else {
      R_type = CONSTRAINT_LE;
    }
    break;
  default:
    assert(false);
  }

  // Construct and swap in the final constraint
  monomial_cmp cmp(*this);
  constraint tmp(R_term, R_type, cmp);
  R.swap(tmp);
}

bool conflict_resolution::evaluate(const constraint& C) const {
  // Calculate the term value
  expr::rational R;
  const monomial_list& monomials = C.get_monomials();
  for (size_t i = 0; i < monomials.size(); ++ i) {
    const monomial& m = monomials[i];
    R += m.a * d_variable_info[m.x].get_value();
  }
  R += C.get_constant();
  // Check if the value satiefies the relation
  switch (C.get_op()) {
  case CONSTRAINT_LE:
    return R.sgn() <= 0;
    break;
  case CONSTRAINT_LT:
    return R.sgn() < 0;
    break;
  case CONSTRAINT_EQ:
    return R.sgn() == 0;
    break;
  default:
    assert(false);
    return true;
  }
}

}
}

#endif
