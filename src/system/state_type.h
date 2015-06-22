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

#include <string>
#include <vector>
#include <cassert>

#include "expr/term_manager.h"
#include "expr/gc_participant.h"

namespace sally {
namespace system {

class state_formula;
class transition_formula;

/**
 * A state type identified by it's id (name) and it's type. The types are
 * managed in the context, and everyone else has const pointers to the types.
 */
class state_type : public expr::gc_participant {

public:

  /** Class of state variables */
  enum var_class {
    /** Current state */
    STATE_CURRENT,
    /** Next state */
    STATE_NEXT
  };

  /** String representation of the variable class */
  static std::string to_string(var_class vc);

  /** Create a new state type of the given type and name */
  state_type(std::string id, expr::term_manager& tm, expr::term_ref type);

  /** Print the state type to stream */
  void to_stream(std::ostream& out) const;

  /** Get the actual type */
  expr::term_ref get_type() const {
    return d_type;
  }

  /** Get the state variable(s) of the class */
  expr::term_ref get_state_type_variable(var_class vc) const;

  /** Use the namespace for the type (pop the namespace yourself) */
  void use_namespace() const;

  /** Use the namespace for the the var class (pop the namespace yourself)  */
  void use_namespace(var_class vc) const;

  /** Given a variable name get the canonical name */
  std::string get_canonical_name(std::string id, var_class vc) const;

  /** Get the variables of the type. */
  const std::vector<expr::term_ref>& get_variables(var_class vc) const;

  /** Check whether the given formula is a state formula for this type */
  bool is_state_formula(expr::term_ref f) const;

  /** Check whether the given formula is a transition formula for this type */
  bool is_transition_formula(expr::term_ref f) const;

  /** Get the term manager for this type */
  expr::term_manager& tm() const { return d_tm; }

  /** Transform the formula from class to another class */
  expr::term_ref change_formula_vars(var_class from, var_class to, expr::term_ref f) const;

  /** GC */
  void gc_collect(const expr::gc_relocator& gc_reloc);

private:

  /** Id of the type */
  std::string d_id;

  /** The term manager */
  expr::term_manager& d_tm;

  /** The actual type describing the state */
  expr::term_ref_strong d_type;

  /** The current state */
  expr::term_ref_strong d_current_state;

  /** The next state */
  expr::term_ref_strong d_next_state;

  /** State variables */
  std::vector<expr::term_ref> d_current_vars;

  /** Next state variables */
  std::vector<expr::term_ref> d_next_vars;

  /** Substitution map for CURRENT -> NEXT */
  expr::term_manager::substitution_map d_subst_current_next;

  /** Substitution map for NEXT -> CURRENT */
  expr::term_manager::substitution_map d_subst_next_current;

};

std::ostream& operator << (std::ostream& out, const state_type& st);

}
}
