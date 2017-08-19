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

#include <vector>
#include <boost/unordered_map.hpp>

#include <mathsat.h>
#include "mathsat5_utils.h"

#include "expr/rational.h"

namespace sally {
namespace smt {

class conflict_resolution {

  /** The mathsat environment */
  msat_env d_env;

  /** Variable ids */
  typedef size_t variable_id;

  /** Null variable */
  static const size_t variable_null = -1;

  /** Map from terms to their ids */
  typedef boost::unordered_map<msat_term, variable_id, mathsat5_hasher, mathsat5_eq> term_to_variable_id_map;

  /** Map from variables to their ids */
  term_to_variable_id_map d_term_to_variable_id_map;

  /** Bound */
  class bound_info {
    /** The value of the bound */
    expr::rational d_v;
    /** Is it a strict bound */
    bool d_is_strict;
    /** Is it infinity */
    bool d_is_infinity;
  public:
    bound_info();
  };

  /** Where does the variable occur (assigned to ease sorting) */
  enum variable_source {
    VARIABLE_B = 0,  // B variable
    VARIABLE_A = 1   // A variable
  };

  /** All information about a variable */
  class variable_info {
    /** Source of the variable */
    variable_source d_source;
    /** The mathsat term of this variable */
    msat_term d_x;
    /** The current lower bound */
    bound_info d_lb;
    /** The current upper bound */
    bound_info d_ub;
  public:
    variable_info();
    variable_info(msat_term x, variable_source source);
    void set_source(variable_source source);
    variable_source get_source() const;
    msat_term get_msat_term() const;
  };

  /** Info on variables */
  std::vector<variable_info> d_variable_info;

  /** Comparison of variables so that B < A, otherwise by mathsat id */
  struct variable_cmp {
    const conflict_resolution& cr;
    bool operator () (variable_id x, variable_id y) const;
    variable_cmp(const conflict_resolution& cr): cr(cr) {}
  };

  /** Add a variable and return it's id */
  variable_id add_variable(msat_term t, variable_source source);

  /** Ids of constraints */
  typedef size_t constraint_id;

  /** Null constraint */
  static const size_t constraint_null = -1;

  /** Map from terms to their ids */
  typedef boost::unordered_map<msat_term, constraint_id, mathsat5_hasher, mathsat5_eq> term_to_constraint_id_map;

  /** Map from variables to their ids */
  term_to_constraint_id_map d_term_to_constraint_id_map;

  /** Types of constraints */
  enum constraint_type {
    CONSTRAINT_LE, // t <= 0
    CONSTRAINT_LT, // t < 0
    CONSTRAINT_EQ  // t == 0
  };

  /** Constraint class */
  enum constraint_source {
    CONSTRAINT_A, // Came from A, or resolution on A constraints
    CONSTRAINT_B, // Came from B
    CONSTRAINT_AB // Came from resolution of A and B constraints
  };

  /**
   * Constraint a*x + b ? 0.
   *
   * Variables are arranged so that x[0] is the top variable.
   */
  struct constraint {

    /** The type of constraint */
    constraint_type type;
    /** The coefficients */
    std::vector<expr::rational> a;
    /** The variables */
    std::vector<variable_id> x;
    /** The constant */
    expr::rational b;

    constraint();

    void to_stream(std::ostream& out) const;
  };

  friend
  std::ostream& operator << (std::ostream& out, const constraint& C);

  /** The constraint */
  std::vector<constraint> d_constraints;

  /** Add a constraint */
  constraint_id add_constraint(msat_term t, constraint_source source);

  /** Add a*t to the constraint C */
  void add_to_constraint(constraint& C, const expr::rational& a, msat_term t, constraint_source source);

public:

  /** Construct the conflict resolver */
  conflict_resolution(msat_env env);

  /** Interpolate between the constraints in a and the constraint b */
  msat_term interpolate(msat_term* a, msat_term b);

};

}
}

#endif
