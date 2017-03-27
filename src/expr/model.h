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

#include "expr/term_manager.h"
#include "expr/value.h"

#include "utils/smart_ptr.h"

#include <map>
#include <vector>
#include <iosfwd>

namespace sally {
namespace expr {

class model {

public:

  typedef std::map<term_ref, value> term_to_value_map;
  typedef term_to_value_map::const_iterator const_iterator;
  typedef term_to_value_map::iterator iterator;
  typedef utils::smart_ptr<model> ref;

  /**
   * Create a model. If undef_to_default is true, it will return default
   * values for undefined variables. Otherwise an exception is thrown.
   */
  model(term_manager& tm, bool undef_to_default);

  /** Copy constructor */
  model(const model& other);

  /** Assignments */
  model& operator = (const model& other);

  /** Clear the model */
  void clear();

  /** Set the value of a variable */
  void set_variable_value(term_ref var, value v);

  /** Get the value of a term in the model (not just variables) */
  value get_variable_value(term_ref var) const;

  /** Get the value of a term in the model (not just variables) */
  value get_variable_value(term_ref var, const expr::term_manager::substitution_map& var_renaming) const;

  /** Get the value of a term in the model (not just variables) */
  value get_term_value(term_ref t) const;

  /** Get the value of a term in the model (not just variables), modulo the renaming (x_t -> x_model) */
  value get_term_value(term_ref t, const expr::term_manager::substitution_map& var_renaming) const;

  /** Is the formula true in the model */
  bool is_true(term_ref f) const ;

  /** Is the formula true in the model, modulo the renaming (x_f -> x_model) */
  bool is_true(term_ref f, const expr::term_manager::substitution_map& var_renaming) const;

  /** Is the formula false in the model */
  bool is_false(term_ref f) const;

  /** Is the formula true in the model, modulo the renaming (x_f -> x_model) */
  bool is_false(term_ref f, const expr::term_manager::substitution_map& var_renaming) const;

  /** Return true if a variable var has a value in the model */
  bool has_value(term_ref var) const;

  /** Get the iterator for the first of var -> value */
  const_iterator values_begin() const;

  /** Get the iterator for the last of var -> value */
  const_iterator values_end() const;

  /** Output to stream */
  void to_stream(std::ostream& out) const;

  /** Only keep variables in the map, and replace them with given substitution */
  void restrict_vars_to(const expr::term_manager::substitution_map& subst);

private:

  /** The term manager */
  term_manager& d_tm;

  /** Undefined variables are interpreted with default values */
  bool d_undef_to_default;

  /** All the variables */
  std::vector<term_ref_strong> d_variables;

  /** The map from variables to their values */
  term_to_value_map d_variable_to_value_map;

  /** True value */
  value d_true;

  /** False value */
  value d_false;

  /** Actual computation */
  value get_term_value_internal(expr::term_ref t, const expr::term_manager::substitution_map& var_renaming, term_to_value_map& cache) const;
};

std::ostream& operator << (std::ostream& out, const model& m);

std::ostream& operator << (std::ostream& out, const model::ref& m);

}
}
