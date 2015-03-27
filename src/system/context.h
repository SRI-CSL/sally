/*
 * context.h
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
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
  context(expr::term_manager& tm, const options& opts, utils::statistics& stats);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_term_manager; }

  /** Add a new state type with the given id (vars : types) */
  void add_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types);

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

  /** Get the transition system with the given id */
  const transition_system* get_transition_system(std::string id) const;

  /** True if id exists */
  bool has_transition_system(std::string id) const;

  /** Get the command line options */
  const options& get_options() const;

  /** Get the statistics */
  const utils::statistics& get_statistics() const;

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
  const options& d_options;

  /** Statistics manager */
  utils::statistics& d_stats;
};


}
}
