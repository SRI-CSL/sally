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

class state_formula;
class transition_formula;

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

  /** Register the formula with the state */
  void register_state_formula(const state_formula* f);

  /** Unregister the formula with the state */
  void unregister_state_formula(const state_formula* f);

  /** Register the transition with the state */
  void register_transition_formula(const transition_formula* f);

  /** Unregister the transition with the state */
  void unregister_transition_formula(const transition_formula* f);

  typedef std::set<const state_formula*> formula_set;

  /** Get the iterator to all formulas of this type */
  formula_set::const_iterator state_formulas_begin() const;

  /** Get the iterator to the end of formulas of this type */
  formula_set::const_iterator state_formulas_end() const;

  typedef std::set<const transition_formula*> transition_formula_set;

  /** Get the iterator to all transition formulas of this type */
  transition_formula_set::const_iterator transition_formulas_begin() const;

  /** Get hte iterator to the end of transition formulas of this type */
  transition_formula_set::const_iterator transition_formulas_end() const;

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

  /** All state formulas of this type */
  formula_set d_state_formulas;

  /** ALl transition formulas of this type */
  transition_formula_set d_transition_formulas;

};

std::ostream& operator << (std::ostream& out, const state_type& st);

}
}
