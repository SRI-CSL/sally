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

conflict_resolution::conflict_resolution(msat_env env)
: d_env(env)
{
}

conflict_resolution::bound_info::bound_info()
: d_is_strict(true)
, d_is_infinity(true)
{}

conflict_resolution::variable_info::variable_info()
: d_source(VARIABLE_AB)
{
  MSAT_MAKE_ERROR_TERM(d_x);
}

conflict_resolution::variable_info::variable_info(msat_term x, variable_source source)
: d_source(source)
, d_x(x)
{
}

void conflict_resolution::variable_info::set_source(variable_source source) {
  if (source != d_source && d_source != VARIABLE_AB) {
    d_source = VARIABLE_AB;
  }
}

conflict_resolution::constraint::constraint()
: type(CONSTRAINT_INEQUALITY)
{
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

  constraint_id t_id = d_constraints.size();
  d_constraints.push_back(constraint());

  return t_id;
}

/** Interpolate between the constraints in a and the constraint b */
msat_term conflict_resolution::interpolate(msat_term* a, msat_term b) {

  TRACE("mathsat5::cr") << "CR: computing interpolant." << std::endl;

  // Add all the constraints
  for (size_t i = 0; !MSAT_ERROR_TERM(a[i]); ++ i) {
    TRACE("mathsat5::cr") << "CR: a[" << i << "]:" << a[i] << std::endl;
    add_constraint(a[i], CONSTRAINT_A);
  }
  TRACE("mathsat5::cr") << "CR: b:" << b << std::endl;
  add_constraint(b, CONSTRAINT_B);

  return b;
}

}
}

#endif
