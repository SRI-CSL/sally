/*
 * state_formula.h
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#pragma once

#include <string>
#include <vector>
#include <cassert>

#include "expr/term_manager.h"

namespace sally {
namespace system {

/**
 * A state type identified by it's id (name) and it's type
 */
class state_type {

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
  state_type(expr::term_manager& tm, std::string id, expr::term_ref type);

  /** Print the state type to stream */
  void to_stream(std::ostream& out) const;

  /** Get the actual type */
  expr::term_ref get_type() const {
    return d_type;
  }

  /** Get the state variable(s) of the class */
  expr::term_ref get_state(var_class vc) const;

  /** Use the namespace for the type (pop the namespace yourself) */
  void use_namespace() const;

  /** Use the namespace for the the var class (pop the namespace yourself)  */
  void use_namespace(var_class vc) const;

  /**
   * Get the variables of the type, the first one will be the struct variable,
   * followed by the struct fields in order of declared.
   */
  const std::vector<expr::term_ref>& get_variables(var_class vc) const;

  /** Check whether the given formula is a state formula for this type */
  bool is_state_formula(expr::term_ref f) const;

  /** Check whether the given formula is a transition formula for this type */
  bool is_transition_formula(expr::term_ref f) const;

  /** Get the term manager for this type */
  expr::term_manager& tm() const { return d_tm; }

  /** Transform the formula from class to another class */
  expr::term_ref change_formula_vars(var_class from, var_class to, expr::term_ref f) const;

private:

  /** The term manager */
  expr::term_manager& d_tm;

  /** The name of the type */
  std::string d_id;

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
