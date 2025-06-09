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

#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "system/transition_system.h"

#include "utils/options.h"
#include "utils/exception.h"
#include "utils/symbol_table.h"
#include "utils/statistics.h"

namespace sally {
namespace system {

/**
 * A context to create and keep track of transition systems, their types,
 * formulas, properties...
 */
class context {

public:

  /** Construct the parser state */
  context(expr::term_manager& tm, options& opts, utils::statistics& stats);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_term_manager; }

  /** Add a new state type with the given id (vars : types) */
  void add_state_type(std::string id,
      const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
      const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types);

  /** Add a state type with the given id (to be managed by the context) */
  void add_state_type(std::string id, state_type* st);

  /** Get the state type with the given id */
  const state_type* get_state_type(std::string id) const;

  /** True if id exists */
  bool has_state_type(std::string id) const;

  /** Add a new state formula with the given id (to be managed by the context) */
  void add_state_formula(std::string id, std::string type_id, expr::term_ref sf);

  /** Add a new state formula with the given id (to be managed by the context) */
  void add_state_formula(std::string id, state_formula* sf);

  /** Get the state formula with the given id */
  const state_formula* get_state_formula(std::string id) const;

  /** True if id exists */
  bool has_state_formula(std::string id) const;

  /** Add a new state transition with the given id (to be managed by the context) */
  void add_transition_formula(std::string id, std::string type_id, expr::term_ref sf);

  /** Add a new state transition with the given id (to be managed by the context) */
  void add_transition_formula(std::string id, transition_formula* tf);

  /** Get the state transition formula with the given id */
  const transition_formula* get_transition_formula(std::string id) const;

  /** True if id exists */
  bool has_transition_formula(std::string id) const;

  /** Add a new state transition system with the given id (to be managed by the context) */
  void add_transition_system(std::string id, transition_system* ts);

  /** Add an assumption to the given transition system (takes over sf). */
  void add_assumption_to(std::string id, state_formula* sf);

  /** Add an assumption to the given transition system (takes over sf). */
  void add_assumption_to(std::string id, transition_formula* tf);

  /** Add an invariant to the given transition system (takes over sf). */
  // void add_invariant_to(std::string id, state_formula* sf);

  /** Get the transition system with the given id */
  const transition_system* get_transition_system(std::string id) const;

  /** True if id exists */
  bool has_transition_system(std::string id) const;

  /** Get the command line options */
  options& get_options() const;

  /** Get the statistics */
  utils::statistics& get_statistics() const;

  /** Set of ids */
  typedef std::set<std::string> id_set;

  /** Get the iterator to all formulas of this type */
  id_set::const_iterator state_formulas_begin(const system::state_type* st) const;

  /** Get the iterator to the end of formulas of this type */
  id_set::const_iterator state_formulas_end(const system::state_type* st) const;

  /** Get the iterator to all transition formulas of this type */
  id_set::const_iterator transition_formulas_begin(const system::state_type* st) const;

  /** Get hte iterator to the end of transition formulas of this type */
  id_set::const_iterator transition_formulas_end(const system::state_type* st) const;

  /** Get the iterator to all transition formulas of this type */
  id_set::const_iterator transition_systems_begin(const system::state_type* st) const;

  /** Get hte iterator to the end of transition formulas of this type */
  id_set::const_iterator transition_systems_end(const system::state_type* st) const;

private:

  /** The term manager */
  expr::term_manager& d_term_manager;

  /** Symbol table for state types */
  utils::symbol_table<const state_type*> d_state_types;

  /** Symbol table for state formulas */
  utils::symbol_table<const state_formula*> d_state_formulas;

  /** Symbol table for state transition formulas */
  utils::symbol_table<const transition_formula*> d_transition_formulas;

  /** Symbol table for transition systems */
  utils::symbol_table<transition_system*> d_transition_systems;

  /** Map from state types to their state formulas */
  std::map<const state_type*, id_set> d_state_types_to_state_formulas;

  /** Map from state types to their transition formulas */
  std::map<const state_type*, id_set> d_state_types_to_transition_formulas;

  /** Map from state_type to their transition systems */
  std::map<const state_type*, id_set> d_state_types_to_transition_systems;

  /** Various options */
  options& d_options;

  /** Statistics manager */
  utils::statistics& d_stats;
};


}
}
