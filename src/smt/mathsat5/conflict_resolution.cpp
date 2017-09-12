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

#include <ap_global0.h>
#include <ap_global1.h>
#include <box.h>
#include <oct.h>
#include <pk.h>
#include <pkeq.h>

#include <gmp.h>

namespace sally {
namespace smt {

std::ostream& operator << (std::ostream& out, const constraint& C) {
  C.to_stream(out);
  return out;
}

std::ostream& operator << (std::ostream& out, const conflict_resolution::variable_info& info) {
  info.to_stream(out);
  return out;
}

std::ostream& operator << (std::ostream& out, const linear_term& info) {
  info.to_stream(out);
  return out;
}

conflict_resolution::conflict_resolution(msat_env env)
: d_env(env)
, d_variable_AB_map(0)
, d_use_apron(false)
, d_domain(DOMAIN_POLKA)
, d_use_widnening(false)
, d_collection_type(COLLECT_BOT)
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

variable_class conflict_resolution::get_variable_class(variable_id x) const {
  return d_variable_info[x].get_class();
}

msat_term conflict_resolution::get_msat_term(variable_id x) const {
  return d_variable_info[x].get_msat_term();
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

constraint_id conflict_resolution::bound_info::get_constraint() const {
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
: d_class(VARIABLE_A)
{
  MSAT_MAKE_ERROR_TERM(d_msat_term);
}

conflict_resolution::variable_info::variable_info(msat_term x, variable_class var_class)
: d_class(var_class)
, d_msat_term(x)
{
}

void conflict_resolution::variable_info::clear_bounds() {
  d_lb.clear();
  d_ub.clear();
}

void conflict_resolution::variable_info::set_class(variable_class var_class) {
  assert(d_class != VARIABLE_B && var_class == VARIABLE_B);
  d_class = var_class;
}

void conflict_resolution::set_use_apron(bool use_apron, apron_domain domain, bool use_widening) {
  d_use_apron = use_apron;
  d_domain = domain;
  d_use_widnening = use_widening;
}

void conflict_resolution::set_collection_type(collection_type type) {
  d_collection_type = type;
}

variable_class conflict_resolution::variable_info::get_class() const {
  return d_class;
}

msat_term conflict_resolution::variable_info::get_msat_term() const {
  return d_msat_term;
}

const expr::rational conflict_resolution::variable_info::get_value() const {
  return d_value;
}

constraint_id conflict_resolution::variable_info::get_lb_constraint() const {
  return d_lb.get_constraint();
}

constraint_id conflict_resolution::variable_info::get_ub_constraint() const {
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

constraint::constraint()
: d_source(CONSTRAINT_A)
, d_op(CONSTRAINT_EQ)
{
}

constraint::constraint(const linear_term& t, constraint_op type, constraint_source source)
: d_source(source)
, d_op(type)
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

constraint::constraint(const linear_term& t, constraint_op type, constraint_source source, const monomial_cmp& cmp)
: d_source(source)
, d_op(type)
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

void constraint::setup_top_variable(const monomial_cmp& cmp) {
  if (d_ax.size() > 0) {
    std::vector<monomial>::iterator max_it = std::max_element(d_ax.begin(), d_ax.end(), cmp);
    std::iter_swap(d_ax.begin(), max_it);
  }
}

linear_term::linear_term(const constraint& C)
: d_b(C.get_constant())
{
  const monomial_list monomials = C.get_monomials();
  monomial_list::const_iterator it = monomials.begin();
  for (; it != monomials.end(); ++ it) {
    const monomial& m = *it;
    d_ax[m.x] += m.a;
  }
}

void linear_term::add(const expr::rational& a, const linear_term& t) {
  assert(this != &t);
  d_b += a*t.d_b;
  var_to_rational_map::const_iterator t_it = t.d_ax.begin();
  for(; t_it != t.d_ax.end(); ++ t_it) {
    d_ax[t_it->first] += a*t_it->second;
  }
}

void linear_term::add(const expr::rational& a, variable_id x) {
  d_ax[x] += a;
}

void linear_term::add(const expr::rational& a) {
  d_b += a;
}

const var_to_rational_map& linear_term::get_monomials() const {
  return d_ax;
}

const expr::rational& linear_term::get_constant() const {
  return d_b;
}

void linear_term::to_stream(std::ostream& out) const {
  var_to_rational_map::const_iterator it = d_ax.begin();
  for (; it != d_ax.end(); ++ it) {
    out << it->second << "*" << "x" << it->first << " + ";
  }
  out << d_b;
}

void constraint::negate() {
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

size_t constraint::size() const {
  return d_ax.size();
}

constraint_source constraint::get_source() const {
  return d_source;
}

variable_id constraint::get_top_variable() const {
  assert(d_ax.size() > 0);
  return d_ax[0].x;
}

const expr::rational& constraint::get_top_coefficient() const {
  assert(d_ax.size() > 0);
  return d_ax[0].a;
}

const monomial_list& constraint::get_monomials() const {
  return d_ax;
}

const expr::rational& constraint::get_constant() const {
  return d_b;
}

void constraint::swap(constraint& C) {
  std::swap(d_source, C.d_source);
  std::swap(d_op, C.d_op);
  std::swap(d_b, C.d_b);
  d_ax.swap(C.d_ax);
}

constraint_op constraint::get_op() const {
  return d_op;
}

void constraint::to_stream(std::ostream& out) const {
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

  switch (d_source) {
  case CONSTRAINT_A:
    out << " A";
    break;
  case CONSTRAINT_B:
    out << " B";
    break;
  }

  out << ")";
}

variable_id conflict_resolution::add_variable(msat_term t, constraint_source source) {

// Class is difficult. Some variables are not A/B, for example Mathsat
  // keeps ITEs that we treat as variables. We want to make sure that B variables 
  // are lower than the A variables. So, if a variable is known to be A or B, we keep it 
  // A or B. Otherwise, we use the constraint source to classify it:
  // - If variable is only in A constraints, we mark it A
  // - Otherwise, the variable is in A and B constraints, so we mark it B
  bool is_A_variable = d_variable_AB_map->find(t) != d_variable_AB_map->end();
  bool is_B_variable = d_variable_BA_map.find(t) != d_variable_BA_map.end();
  variable_class var_class;
  if (is_A_variable) var_class = VARIABLE_A;
  else if (is_B_variable) var_class = VARIABLE_B;
  else if (source == CONSTRAINT_A) var_class = VARIABLE_A;
  else var_class = VARIABLE_B;
  
  // Check if the variable is already there
  // - marked AB, and comes from B -> B
  // - markes A, and comes from B -> B
  term_to_variable_id_map::const_iterator find = d_term_to_variable_id_map.find(t);
  if (find != d_term_to_variable_id_map.end()) {
    variable_id t_id = find->second;
    if (d_variable_info[t_id].get_class() != VARIABLE_B && var_class == VARIABLE_B) {
      d_variable_info[t_id].set_class(VARIABLE_B);      
    }
    return find->second;
  }
  
  variable_id t_id = d_variable_info.size();
  d_variable_info.push_back(variable_info(t, var_class));
  d_term_to_variable_id_map[t] = t_id;
  d_top_var_to_constraint.push_back(constraint_list());
  assert(d_variable_info.size() == d_top_var_to_constraint.size());

  return t_id;
}

variable_id conflict_resolution::get_variable(msat_term t) const {
  term_to_variable_id_map::const_iterator find = d_term_to_variable_id_map.find(t);
  if (find != d_term_to_variable_id_map.end()) {
    return find->second;
  } else {
    return variable_null;
  }
}

void conflict_resolution::add_to_watchlist(constraint_id C_id) {
  const constraint& C = d_constraints[C_id];
  d_top_var_to_constraint[C.get_top_variable()].push_back(C_id);
}

const conflict_resolution::constraint_list& conflict_resolution::get_watchlist(variable_id x) const {
  return d_top_var_to_constraint[x];
}

constraint_id conflict_resolution::add_constraint(msat_term t, constraint_source source) {

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
  d_constraints.push_back(constraint(constraint_term, type, source));
  constraint& C = d_constraints.back();

  // Negate if necessary
  if (is_not) {
    C.negate();
  }

  TRACE("mathsat5::cr") << "CR: added constraint: " << C << std::endl;

  return t_id;
}

void conflict_resolution::add_to_linear_term(linear_term& term, const expr::rational& a, msat_term t, constraint_source source) {

  if (msat_term_is_constant(d_env, t) || msat_term_is_term_ite(d_env, t)) {
    // Variables
    variable_id x = add_variable(t, source);
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

bool variable_cmp::operator () (variable_id x, variable_id y) const {

  // Sort the variables so that B < A, otherwise by mathsat id
  variable_class x_class = cr.get_variable_class(x);
  variable_class y_class = cr.get_variable_class(y);

  // If different classes, then sort as B < A (as in enum)
  if (x_class != y_class) {
    return x_class < y_class;
  }

  // Same class, sort by mathsat id
  msat_term x_term = cr.get_msat_term(x);
  msat_term y_term = cr.get_msat_term(y);
  return msat_term_id(x_term) < msat_term_id(y_term);
}

bool monomial_cmp::operator () (const monomial& ax, const monomial& by) const {

  // Sort the variables so that B < A, otherwise by mathsat id
  variable_class x_class = cr.get_variable_class(ax.x);
  variable_class y_class = cr.get_variable_class(by.x);

  // If different classes, then sort as B < A (as in enum)
  if (x_class != y_class) {
    return x_class < y_class;
  }

  // Same class, sort by mathsat id
  msat_term x_term = cr.get_msat_term(ax.x);
  msat_term y_term = cr.get_msat_term(by.x);
  size_t x_term_id = msat_term_id(x_term);
  size_t y_term_id = msat_term_id(y_term);
  if (x_term_id != y_term_id) {
    return x_term_id < y_term_id;
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
  msat_term new_b[2];
  new_b[0] = b;
  MSAT_MAKE_ERROR_TERM(new_b[1]);
  return interpolate(a, new_b);
}

msat_term conflict_resolution::interpolate(msat_term* a, msat_term* b) {

  TRACE("mathsat5::cr") << "CR: computing interpolant." << std::endl;

  msat_term error;
  MSAT_MAKE_ERROR_TERM(error);

  // All A constraints, to remember what to keep in the interpolant
  constraint_set A_constraints;

  // A: Add all the constraints
  for (size_t i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
    TRACE("mathsat5::cr") << "CR: a[" << i << "]:" << a[i] << std::endl;
    if (!can_interpolate(a[i])) {
      return error;
    }
    constraint_id c_id = add_constraint(a[i], CONSTRAINT_A);
    A_constraints.insert(c_id);
  }
  for (size_t i = 0; !MSAT_ERROR_TERM(b[i]); ++ i) {
    TRACE("mathsat5::cr") << "CR: b:" << b[i] << std::endl;
    if (!can_interpolate(b[i])) {
      msat_term error;
      MSAT_MAKE_ERROR_TERM(error);
      return error;
    }
    add_constraint(b[i], CONSTRAINT_B);
  }
  
  // if |A| = 0 => interpolant = T
  if (A_constraints.size() == 0) {
    return msat_make_true(d_env);
  }
  if (A_constraints.size() == d_constraints.size()) {
    return msat_make_false(d_env);
  }

    // If we have some releationship between variables, run apron
  if (d_use_apron && d_variable_AB_map->size()) {
    size_t old_size = d_constraints.size();
    learn_with_apron();
    for (constraint_id c_id = old_size; c_id < d_constraints.size(); ++ c_id) {
      A_constraints.insert(c_id);
    }
  }
  
  // B: Order the variables B -> AB -> A
  variable_cmp var_cmp(*this);
  std::vector<variable_id> all_vars;
  for (variable_id x = 0; x < d_variable_info.size(); ++ x) {
    all_vars.push_back(x);
  }
  std::sort(all_vars.begin(), all_vars.end(), var_cmp);

  // Setup the constraints: setup_top_variable variables
  monomial_cmp mon_cmp(*this);
  for (size_t C_id = 0; C_id < d_constraints.size(); ++ C_id) {
    constraint& C = d_constraints[C_id];
    C.setup_top_variable(mon_cmp);
    add_to_watchlist(C_id);
  }

  if (output::trace_tag_is_enabled("mathsat5::cr")) {
    TRACE("mathsat5::cr") << "CR: variable_order:" << std::endl;
    for (size_t i = 0; i < all_vars.size(); ++ i) {
      TRACE("mathsat5::cr") << "- x" << all_vars[i];
      TRACE("mathsat5::cr") << " (" << (d_variable_info[all_vars[i]].get_class() == VARIABLE_A ? "A" : "B") << "):";
      const constraint_list& x_cstrs = get_watchlist(all_vars[i]);
      constraint_list::const_iterator it = x_cstrs.begin();
      for (; it != x_cstrs.end(); ++ it) {
        TRACE("mathsat5::cr") << " " << d_constraints[*it];
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
    TRACE("mathsat5::cr") << "CR: propagating on x" << x << ": " << d_variable_info[x] << std::endl;

    // All the constraints where x is the top variable
    const constraint_list& x_constraints = get_watchlist(x);
    constraint_list::const_iterator it = x_constraints.begin();
    for (; it != x_constraints.end(); ++ it) {
      // Propagate new bound if implied by this constraint  
      constraint_id C_id = *it;
      assert(d_constraints[C_id].get_top_variable() == x);
      ok = ok && propagate(C_id);
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

      TRACE("mathsat5::cr") << "CR: resolving:" << "C_lb: " << lb_C << std::endl;
      TRACE("mathsat5::cr") << "CR: resolving:" << "C_ub: " << ub_C << std::endl;

      // Now resolve the constraints
      resolve(lb_C, ub_C, R);
      assert(!evaluate(R));
      TRACE("mathsat5::cr") << "CR: resolvent:" << "R: " << R << std::endl;

      if (d_collection_type == COLLECT_BOT) {
        // A-derived constraints that are resolved with constraints from B
        if (ub_C.get_source() == CONSTRAINT_A && lb_C.get_source() == CONSTRAINT_B) {
          TRACE("mathsat5::cr") << "CR: adding to interpolant: " << ub_C << std::endl;
          interpolants.insert(ub_C_id);
        }
        if (ub_C.get_source() == CONSTRAINT_B && lb_C.get_source() == CONSTRAINT_A) {
          TRACE("mathsat5::cr") << "CR: adding to interpolant: " << lb_C << std::endl;
          interpolants.insert(lb_C_id);
        }
      }
      if (d_collection_type == COLLECT_TOP) {
        // Keep any constraints originally in A
        if (d_variable_info[x].get_class() != VARIABLE_A) {
          if (A_constraints.count(lb_C_id) > 0) {
            interpolants.insert(lb_C_id);
          }
          if (A_constraints.count(ub_C_id) > 0) {
            interpolants.insert(ub_C_id);
          }
        }
      }

      // If resolvent is empty, we're done
      if (R.size() == 0) {
        if (output::trace_tag_is_enabled("mathsat5::cr")) {
          constraint_set::const_iterator it = interpolants.begin();
          for (bool first = true; it != interpolants.end(); ++ it) {
            if (!first) TRACE("mathsat5::cr") << ", ";
            TRACE("mathsat5::cr") << d_constraints[*it];
            first = false;
          }
          TRACE("mathsat5::cr") << std::endl;
        }
        return construct_msat_term(interpolants);
      } else {

        // Check if to add to the interpolant
        variable_id x_new = R.get_top_variable();

        // Add the resolvent if we went from A -> B
        if (d_collection_type == COLLECT_TOP) {
          if (d_variable_info[x].get_class() == VARIABLE_A &&
              d_variable_info[x_new].get_class() != VARIABLE_A) {
            interpolants.insert(R_id);
          }
        }

        // Backtrack to the new top variable
        x = x_new;
        while (all_vars[k] != x) {
          d_variable_info[all_vars[k]].clear_bounds();
          k --;
        }

        // Add the constraint to list of x
        add_to_watchlist(R_id);

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
  return error;
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

msat_term conflict_resolution::construct_msat_term(const constraint_vector& list) {
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

  // The source of the final constraint
  constraint_source source = CONSTRAINT_A;
  if (C1.get_source() == CONSTRAINT_B || C2.get_source() == CONSTRAINT_B) {
    source = CONSTRAINT_B;
  }

  // Construct and swap in the final constraint
  monomial_cmp cmp(*this);
  constraint tmp(R_term, R_type, source, cmp);
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

void conflict_resolution::set_var_to_var_map(const term_to_term_map* x_to_x_next) {
  d_variable_AB_map = x_to_x_next;
  d_variable_BA_map.clear();
  term_to_term_map::const_iterator it = x_to_x_next->begin();
  for (; it != x_to_x_next->end(); ++ it) {
    msat_term x = it->first;
    msat_term x_next = it->second;
    assert(d_variable_BA_map.find(x_next) == d_variable_BA_map.end());
    d_variable_BA_map[x_next] = x;
  }
}

class apron_helper {

  ap_manager_t* d_man;
  
  ap_coeff_t d_coeff_tmp;
  mpq_t d_mpq_coeff_tmp;

  std::vector<char*> d_var_names;

  ap_environment_t* d_env;

  // Get the Apron version of the constraint type */
  static
  ap_constyp_t op_to_constyp(constraint_op op);

  // Get the constraint op from Apron constraint type */
  static
  constraint_op constyp_to_op(ap_constyp_t type);
  
public:

  apron_helper(conflict_resolution::apron_domain, size_t n_variables);
  ~apron_helper();
    
  // Get the manager
  ap_manager_t* man() { return d_man; }

  // Construct Apron linear constraint from given constraint 
  ap_lincons1_t make(const constraint& C);

  // Construct an Apron abstraction from vector of constraints 
  ap_abstract1_t make(std::vector<ap_lincons1_t>& constraints);

  // Project out all variables except given 
  ap_abstract1_t eliminate_except(ap_abstract1_t constraints, const std::vector<size_t>& keep_variables);
  
  // Rename from given variables to the 
  ap_abstract1_t rename(ap_abstract1_t constraints,
    const std::vector<size_t>& from, 
    const std::vector<size_t>& to);

  // Join
  ap_abstract1_t join(ap_abstract1_t c1, ap_abstract1_t c2);

  // Widen
  ap_abstract1_t widen(ap_abstract1_t c1, ap_abstract1_t c2);

  // Add to constraints
  void to_constraints(ap_abstract1_t a, std::vector<constraint>& out);
};

apron_helper::apron_helper(conflict_resolution::apron_domain domain, size_t n_variables)
: d_man(0) 
{
  switch (domain) {
  case conflict_resolution::DOMAIN_BOX:
    d_man = box_manager_alloc();
    break;
  case conflict_resolution::DOMAIN_OCT:
    d_man = oct_manager_alloc();
    break;
  case conflict_resolution::DOMAIN_POLKA:
    d_man = pk_manager_alloc(true);
    break;
  default: 
    assert(false);
  }
  ap_coeff_init(&d_coeff_tmp, AP_COEFF_SCALAR);
  mpq_init(d_mpq_coeff_tmp); 
  for (size_t i = 0; i < n_variables; ++ i) {
    std::stringstream ss;
    ss << "x" << i;
    d_var_names.push_back(strdup(ss.str().c_str()));
  }
  d_env = ap_environment_alloc(0, 0, (ap_var_t*) &d_var_names[0], n_variables);
}

apron_helper::~apron_helper() {
  for (size_t i = 0; i < d_var_names.size(); ++ i) {
    free(d_var_names[i]);
  }
  ap_environment_free(d_env);
  mpq_clear(d_mpq_coeff_tmp);
  ap_coeff_clear(&d_coeff_tmp);
  ap_manager_free(d_man);
}

ap_constyp_t apron_helper::op_to_constyp(constraint_op op)
{
  switch (op) {
  case CONSTRAINT_LE:
    return AP_CONS_SUPEQ;
  case CONSTRAINT_LT:
    return AP_CONS_SUP;
  case CONSTRAINT_EQ:
    return AP_CONS_EQ;
  default:
    assert(false);
  }
  return AP_CONS_EQ;
}

constraint_op apron_helper::constyp_to_op(ap_constyp_t type)
{
  switch (type) {
  case AP_CONS_SUPEQ:
    return CONSTRAINT_LE;
  case AP_CONS_SUP:
    return CONSTRAINT_LT;
  case AP_CONS_EQ:
    return CONSTRAINT_EQ;
  default:
    assert(false);
  }
  return CONSTRAINT_EQ;
}


ap_lincons1_t apron_helper::make(const constraint& C)
{
  ap_linexpr1_t expr = ap_linexpr1_make(d_env, AP_LINEXPR_SPARSE, C.size());
  ap_constyp_t C_type = op_to_constyp(C.get_op());
  ap_lincons1_t cstr = ap_lincons1_make(C_type, &expr, NULL);
  const monomial_list& monomials = C.get_monomials();
  for (monomial_list::const_iterator it = monomials.begin(); it != monomials.end(); ++ it) {
    variable_id x = it->x;
    mpq_set(d_mpq_coeff_tmp, it->a.mpq().get_mpq_t());
    mpq_neg(d_mpq_coeff_tmp, d_mpq_coeff_tmp); // Negate, our OPs are opposite of Aprons
    ap_coeff_set_scalar_mpq(&d_coeff_tmp, d_mpq_coeff_tmp);
    ap_lincons1_set_coeff(&cstr, (ap_var_t) d_var_names[x], &d_coeff_tmp);
  }
  mpq_set(d_mpq_coeff_tmp, C.get_constant().mpq().get_mpq_t());
  mpq_neg(d_mpq_coeff_tmp, d_mpq_coeff_tmp); // Negate, our OPs are opposite of Aprons
  ap_coeff_set_scalar_mpq(&d_coeff_tmp, d_mpq_coeff_tmp);
  ap_lincons1_set_cst(&cstr, &d_coeff_tmp);
  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "C:"); ap_lincons1_fprint(stderr, &cstr); fprintf(stderr, "\n");
  }
  return cstr;
}

ap_abstract1_t apron_helper::make(std::vector<ap_lincons1_t>& constraints) 
{
  ap_lincons1_array_t array = ap_lincons1_array_make(d_env, constraints.size());
  for (size_t i = 0; i < constraints.size(); ++ i) {
    ap_lincons1_array_set(&array, i, &constraints[i]);
  }
  ap_abstract1_t result = ap_abstract1_of_lincons_array(d_man, d_env, &array);
  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "Abs:\n");
    ap_abstract1_fprint(stderr, d_man, &result);
  }
  ap_lincons1_array_clear(&array);

  return result;
}

void apron_helper::to_constraints(ap_abstract1_t a, std::vector<constraint>& out) {
  ap_lincons1_array_t c_array = ap_abstract1_to_lincons_array(d_man, &a);
  size_t c_array_size = ap_lincons1_array_size(&c_array);  
  for (size_t i = 0; i < c_array_size; ++ i) {
    // Get the apron expressions
    ap_lincons1_t c = ap_lincons1_array_get(&c_array, i);
    ap_constyp_t* c_type = ap_lincons1_constypref(&c);

    ap_linexpr1_t c_expr = ap_lincons1_linexpr1ref(&c);
    // Allocate the new constraint
    linear_term C_term;
    // Get the constant 
    ap_linexpr1_get_cst(&d_coeff_tmp, &c_expr);
    ap_mpq_set_scalar(d_mpq_coeff_tmp, d_coeff_tmp.val.scalar, MPFR_RNDD); // There should be no rounding 
    mpq_neg(d_mpq_coeff_tmp, d_mpq_coeff_tmp); // Negate, our OPs are opposite of Aprons
    C_term.add(expr::rational(d_mpq_coeff_tmp));
    // Add other terms 
    {
      ap_coeff_t* c_expr_pcoeff;
      ap_var_t c_expr_var;
      size_t i;
      ap_linexpr1_ForeachLinterm1(&c_expr, i, c_expr_var, c_expr_pcoeff) {
        ap_mpq_set_scalar(d_mpq_coeff_tmp, c_expr_pcoeff->val.scalar, MPFR_RNDD); // There should be no rounding
        mpq_neg(d_mpq_coeff_tmp, d_mpq_coeff_tmp); // Negate, our OPs are opposite of Aprons
        expr::rational a(d_mpq_coeff_tmp); 
        variable_id x; // Variable we read from the string such as "x1"
        sscanf(((char*)c_expr_var) + 1, "%zu", &x);
        C_term.add(a, x);
      }
    }
    // The constraint type 
    constraint_op C_op = constyp_to_op(*c_type);
    // Add the constraint
    out.push_back(constraint(C_term, C_op, CONSTRAINT_A));
  }
  ap_lincons1_array_clear(&c_array);
}

ap_abstract1_t apron_helper::eliminate_except(ap_abstract1_t constraints, const std::vector<size_t>& keep)
{
  // Variables for Apron
  std::vector<char*> keep_names;
  for (size_t i = 0; i < keep.size(); ++ i) {
    keep_names.push_back(d_var_names[keep[i]]);
  }
  // Make the environment
  ap_environment_t* env = ap_environment_alloc(0, 0, (ap_var_t*) &keep_names[0], keep_names.size());
  // Eliminate 
  ap_abstract1_t result = ap_abstract1_change_environment(d_man, false, &constraints, env, false);

  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "Elimination Abs:\n");
    ap_abstract1_fprint(stderr, d_man, &result);
  }

  // Get rid of the environment
  ap_environment_free(env);

  return result;
}

ap_abstract1_t apron_helper::rename(ap_abstract1_t constraints,
  const std::vector<size_t>& from, 
  const std::vector<size_t>& to)
{
  assert(from.size() == to.size());
  size_t n_vars = from.size();

  // Variables for Apron
  std::vector<char*> from_names, to_names;
  for (size_t i = 0; i < n_vars; ++ i) {
    from_names.push_back(d_var_names[from[i]]);
  }
  for (size_t i = 0; i < n_vars; ++ i) {
    to_names.push_back(d_var_names[to[i]]);
  }
    
  // Rename
  ap_abstract1_t result = ap_abstract1_rename_array(d_man, false, &constraints, (ap_var_t*) &from_names[0], (ap_var_t*) &to_names[0], n_vars);
  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "Renamed Abs:\n");
    ap_abstract1_fprint(stderr, d_man, &result);
  }

  return result;
}

ap_abstract1_t apron_helper::join(ap_abstract1_t c1, ap_abstract1_t c2) {
  ap_abstract1_t result = ap_abstract1_join(d_man, false, &c1, &c2);
  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "Join Abs:\n");
    ap_abstract1_fprint(stderr, d_man, &result);
  }
  return result;
}

ap_abstract1_t apron_helper::widen(ap_abstract1_t c1, ap_abstract1_t c2) {
  ap_abstract1_t result = ap_abstract1_widening(d_man, &c1, &c2);
  if (output::trace_tag_is_enabled("mathsat5::apron")) {
    fprintf(stderr, "Widen Abs:\n");
    ap_abstract1_fprint(stderr, d_man, &result);
  }
  return result;
}

void conflict_resolution::learn_with_apron() {

  TRACE("mathsat5::apron") << "Learning with Apron." << std::endl;

  assert(d_variable_AB_map);

  // Separate the variables
  std::vector<variable_id> state_variables, next_variables;
  std::set<variable_id> state_variables_set, next_variables_set;
  for (variable_id x = 0; x < d_variable_info.size(); ++ x) {
    if (d_variable_info[x].get_class() == VARIABLE_A && state_variables_set.count(x) == 0) {
      // State variable to add
      msat_term x_term = d_variable_info[x].get_msat_term();
      term_to_term_map::const_iterator x_find = d_variable_AB_map->find(x_term);
      if (x_find != d_variable_AB_map->end()) {
        variable_id x_next = add_variable(x_find->second, CONSTRAINT_A);
        state_variables.push_back(x);
        state_variables_set.insert(x);
        next_variables.push_back(x_next);
        next_variables_set.insert(x_next);
      }
    } 
    if (d_variable_info[x].get_class() == VARIABLE_B && next_variables_set.count(x) == 0) {
      // Next variable to add
      msat_term x_term = d_variable_info[x].get_msat_term();
      term_to_term_map::const_iterator x_find = d_variable_BA_map.find(x_term);
      if (x_find != d_variable_BA_map.end()) {
        variable_id x_prev = add_variable(x_find->second, CONSTRAINT_B);
        state_variables.push_back(x_prev);
        state_variables_set.insert(x_prev);
        next_variables.push_back(x);
        next_variables_set.insert(x);
      }
    } 
  }

  size_t n_vars = d_variable_info.size();
  apron_helper apron(d_domain, n_vars);

  // Apronize all A constraints
  std::vector<ap_lincons1_t> A_constraints;
  for (constraint_id C_id = 0; C_id < d_constraints.size(); ++ C_id) {
    const constraint& C = d_constraints[C_id];
    if (C.get_source() == CONSTRAINT_A) {
      ap_lincons1_t cstr = apron.make(C);
      A_constraints.push_back(cstr);
    }
  }

  // All A constraints into an abstract domain element
  ap_abstract1_t constraints = apron.make(A_constraints);

  // Separate the constraints into state and next
  ap_abstract1_t state = apron.eliminate_except(constraints, state_variables);
  ap_abstract1_t next = apron.eliminate_except(constraints, next_variables);
  
  // Rename variables
  ap_abstract1_t state_next = apron.rename(state, state_variables, next_variables);

  // Join for the final result
  ap_abstract1_t join = apron.join(state_next, next);

  // Widening if asked
  ap_abstract1_t widen;
  if (d_use_widnening) {
    widen = apron.widen(state_next, join);
  }

  // Add the constraints
  if (d_use_widnening) {
    apron.to_constraints(widen, d_constraints);
  } else {
    apron.to_constraints(join, d_constraints);
  }

  // Clear the abstract values
  ap_abstract1_clear(apron.man(), &constraints);
  ap_abstract1_clear(apron.man(), &state);
  ap_abstract1_clear(apron.man(), &next);
  ap_abstract1_clear(apron.man(), &state_next);
  ap_abstract1_clear(apron.man(), &join);
  if (d_use_widnening) {
    ap_abstract1_clear(apron.man(), &widen);
  }
}

}
}

#endif
