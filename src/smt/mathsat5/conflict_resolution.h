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

#include <list>
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
  static const variable_id variable_null = -1;

  /** Ids of constraints */
  typedef size_t constraint_id;

  /** Null constraint */
  static const size_t constraint_null = -1;

  /** Map from terms to their ids */
  typedef boost::unordered_map<msat_term, variable_id, mathsat5_hasher, mathsat5_eq> term_to_variable_id_map;

  /** Map from variables to their ids */
  term_to_variable_id_map d_term_to_variable_id_map;

  /** Bound */
  class bound_info {
    /** The value of the bound */
    expr::rational d_bound;
    /** Is it a strict bound */
    bool d_is_strict;
    /** Is it infinity */
    bool d_is_infinity;
    /** Constraint responsible for the bound */
    constraint_id d_constraint;
  public:

    /** Construct empty bound info (strict infinity with null constraint) */
    bound_info();

    /** Reset to empty bound info (strict infinity with null constraint) */
    void clear();

    /** Is this an infinity bound? */
    bool is_infinity() const;

    /** Is this a strict bound (i.e. doesn't include the bound) */
    bool is_strict() const;

    /** Get the actual bound */
    const expr::rational get_bound() const;

    /** Get the responsible constraint */
    constraint_id get_constraint() const;

    /** Set the values */
    void set(const expr::rational& bound, bool is_strict, constraint_id C_id);

    /** Check if the two bounds are consistent */
    static
    bool consistent(const bound_info& lb, const bound_info& ub);

  };

  /** Where does the variable occur (assigned to ease sorting) */
  enum variable_class {
    VARIABLE_B = 0,  // B variable (can occur in B and A)
    VARIABLE_A = 1   // A variable (occurs only in A)
  };

  /** All information about a variable */
  class variable_info {

    /** Class of the variable */
    variable_class d_class;
    /** The mathsat term of this variable */
    msat_term d_msat_term;
    /** The current lower bound */
    bound_info d_lb;
    /** The current upper bound */
    bound_info d_ub;
    /** Current value of the variable */
    expr::rational d_value;

  public:

    variable_info();
    variable_info(msat_term x, variable_class var_class);

    /** Clear the bounds to -inf, +inf */
    void clear_bounds();

    /** Add another class of this variable variable */
    void add_class(variable_class var_class);

    /** Get the class of the variable */
    variable_class get_class() const;

    /** Get the mathsat term of this variable */
    msat_term get_msat_term() const;

    /** Get the assigned value of the variable */
    const expr::rational get_value() const;

    /** Get the lower bound constraint */
    constraint_id get_lb_constraint() const;
    /** Get the upper bound constraint */
    constraint_id get_ub_constraint() const;

    /**
     * Set lower bound x > bound if is_strict = true, or x >= bound if
     * is_strict = false. Returns true if no conflict.
     * */
    bool set_lower_bound(const expr::rational& bound, bool is_strict, constraint_id C_id);

    /**
     * Set upper bound x < bound if is_strict = true, or x <= bound if
     * is_strict = false. Returns true if no conflict.
     */
    bool set_upper_bound(const expr::rational& bound, bool is_strict, constraint_id C_id);

    /**
     * Pick a value for this between it's bounds. Return true if successful,
     * and false no value between the bounds.
     */
    bool pick_value();

    /** Print to stream */
    void to_stream(std::ostream& out) const;
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
  variable_id add_variable(msat_term t, variable_class var_class);

  /** Map from terms to their ids */
  typedef boost::unordered_map<msat_term, constraint_id, mathsat5_hasher, mathsat5_eq> term_to_constraint_id_map;

  /** Map from variables to their ids */
  term_to_constraint_id_map d_term_to_constraint_id_map;

  /** Types of constraints */
  enum constraint_op {
    CONSTRAINT_LE, // t <= 0
    CONSTRAINT_LT, // t < 0
    CONSTRAINT_EQ  // t == 0
  };

  /** Constraint class */
  enum constraint_source {
    CONSTRAINT_A, // Came from A assertions
    CONSTRAINT_B, // Came from B assertions
  };

  struct linear_term;

  struct monomial {
    expr::rational a;
    variable_id x;
    monomial(const expr::rational a, variable_id x): a(a), x(x) {}
  };

  typedef std::vector<monomial> monomial_list;

  /** Comparison of monomials so that B < A, otherwise by mathsat id */
  struct monomial_cmp {
    const conflict_resolution& cr;
    bool operator () (const monomial& x, const monomial& y) const;
    monomial_cmp(const conflict_resolution& cr): cr(cr) {}
  };

  /**
   * Constraint a*x + b ? 0.
   *
   * Variables are arranged so that x[0] is the top variable.
   */
  class constraint {

    /** Where does the derivation of this constraint come from */
    constraint_source d_source;
    /** The type of constraint */
    constraint_op d_op;
    /** The coefficients */
    monomial_list d_ax;
    /** The constant */
    expr::rational d_b;

  public:

    /** Empty constraint (0 = 0) */
    constraint();

    /** Constraint from pre-constraint (not ordered properly) */
    constraint(const linear_term& C, constraint_op type, constraint_source source);

    /** Constraint from pre-constraint */
    constraint(const linear_term& C, constraint_op type, constraint_source source, const monomial_cmp& cmp);

    /** Order an orderered constraint */
    void setup_top_variable(const monomial_cmp& cmp);

    /** Negate the constraint in place */
    void negate();

    /** Returns the number of variables */
    size_t size() const;

    /** Get the source of the constraint derivation */
    constraint_source get_source() const;

    /** Get the top variable (x[0]) */
    variable_id get_top_variable() const;

    /** Get the coeffficient along the top variable */
    const expr::rational& get_top_coefficient() const;

    /** Get all monomials (ax) */
    const monomial_list& get_monomials() const;

    /** Get the constant (b) */
    const expr::rational& get_constant() const;

    /** Get the type of the variable */
    constraint_op get_op() const;

    /** Swap two constraint */
    void swap(constraint& C);

    /** Print the constraint to stream */
    void to_stream(std::ostream& out) const;
  };

  /** The constraint */
  std::vector<constraint> d_constraints;

  typedef std::vector<constraint_id> constraint_vector;
  typedef std::list<constraint_id> constraint_list;
  typedef std::set<constraint_id> constraint_set;

  /** Map from top variables to constraints */
  std::vector<constraint_list> d_top_var_to_constraint;

  /** Add the constraint to watchlist */
  void add_to_watchlist(constraint_id C_id);

  /** Get the watchlist of variable */
  const constraint_list& get_watchlist(variable_id x) const;

  typedef boost::unordered_map<variable_id, expr::rational> var_to_rational_map;

  /** ax + b */
  class linear_term {
    var_to_rational_map d_ax;
    expr::rational d_b;
  public:
    /** 0 linear term */
    linear_term() {}
    /** Get the linear term from C */
    linear_term(const constraint& C);

    /** Add a*x to the linear term */
    void add(const expr::rational& a, variable_id x);
    /** Add a to the linear term */
    void add(const expr::rational& a);
    /** Add a*t to this term */
    void add(const expr::rational& a, const linear_term& t);

    /** Get the monomials from a*x as a map */
    const var_to_rational_map& get_monomials() const;
    /** Get the constant b */
    const expr::rational& get_constant() const;

    /** Print to stream */
    void to_stream(std::ostream& out) const;
  };

  /** Add a constraint. If negated = true, add negated. */
  constraint_id add_constraint(msat_term t, constraint_source source);

  /** Add a*t to the constraint linear term. Also add any variables. */
  void add_to_linear_term(linear_term& term, const expr::rational& a, msat_term t, constraint_source source);

  /** Propagate constraint C, returns true if no conflict. */
  bool propagate(constraint_id C_id);

  /** Return the conjunction of constraints */
  msat_term construct_msat_term(const constraint& C);

  /** Return the conjunction of constraints */
  msat_term construct_msat_term(const constraint_vector& list);

  /** Return the conjunction of constraints */
  msat_term construct_msat_term(const constraint_set& set);

  /** Resolve the constraints C1 and C2 into R */
  void resolve(const constraint& C1, const constraint& C2, constraint& R) const;

  /** Evaluate a constraint */
  bool evaluate(const constraint& C) const;

  /**
   * Can we handle this constraint (only inequalities, negations of
   * inequalities and equalities.
   */
  bool can_interpolate(msat_term t) const;

  friend
  std::ostream& operator << (std::ostream& out, const constraint& C);

  friend
  std::ostream& operator << (std::ostream& out, const variable_info& info);

  friend
  std::ostream& operator << (std::ostream& out, const linear_term& info);

public:

  /** Construct the conflict resolver */
  conflict_resolution(msat_env env);

  /** Interpolate between the constraints in a and the constraint b. */
  msat_term interpolate(msat_term* a, msat_term b);

  /** Interpolate between the constraints in a and the constraint b. */
  msat_term interpolate(msat_term* a, msat_term* b);

};

}
}

#endif
