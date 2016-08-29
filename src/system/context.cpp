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

#include "system/context.h"

#include <iostream>

namespace sally {
namespace system {

context::context(expr::term_manager& tm, options& opts, utils::statistics& stats)
: d_term_manager(tm)
, d_state_types("state types")
, d_state_formulas("state formulas")
, d_transition_formulas("state transition formulas")
, d_transition_systems("state transition systems")
, d_options(opts)
, d_stats(stats)
{
}

void context::add_state_type(std::string id, state_type* st) {
  if (d_state_types.has_entry(id)) {
    delete st; // Context owns it, so delete it
    throw exception(id + " already declared");
  }
  d_state_types.add_entry(id, st);
  d_state_types_to_state_formulas[st] = id_set();
  d_state_types_to_transition_formulas[st] = id_set();
  d_state_types_to_transition_systems[st] = id_set();
}

void context::add_state_type(std::string id,
    const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
    const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types)
{
  expr::term_ref state_vars_struct = tm().mk_struct_type(state_vars, state_types);
  expr::term_ref input_vars_struct = tm().mk_struct_type(input_vars, input_types);
  add_state_type(id, new state_type(id, tm(), state_vars_struct, input_vars_struct));
}

const state_type* context::get_state_type(std::string id) const {
  if (!d_state_types.has_entry(id)) {
    throw exception(id + " not declared");
  }
  return d_state_types.get_entry(id);
}

bool context::has_state_type(std::string id) const {
  return d_state_types.has_entry(id);
}

void context::add_state_formula(std::string id, state_formula* sf) {
  if (d_state_formulas.has_entry(id)) {
    delete sf; // Context owns it, so delete it
    throw exception(id + "already declared");
  }
  if (d_state_types_to_state_formulas.find(sf->get_state_type()) == d_state_types_to_state_formulas.end()) {
    throw exception("Unknown state type");
  }
  d_state_formulas.add_entry(id, sf);
  d_state_types_to_state_formulas[sf->get_state_type()].insert(id);
}

void context::add_state_formula(std::string id, std::string type_id, expr::term_ref f) {
  const state_type* st = get_state_type(type_id);
  state_formula* sf = new state_formula(tm(), st, f);
  add_state_formula(id, sf);
}

const state_formula* context::get_state_formula(std::string id) const {
  if (!d_state_formulas.has_entry(id)) {
    throw exception(id + " not declered");
  }
  return d_state_formulas.get_entry(id);
}

bool context::has_state_formula(std::string id) const {
  return d_state_formulas.has_entry(id);
}

void context::add_transition_formula(std::string id, transition_formula* tf) {
  if (d_transition_formulas.has_entry(id)) {
    delete tf;
    throw exception(id + " already declared");
  }
  if (d_state_types_to_transition_formulas.find(tf->get_state_type()) == d_state_types_to_transition_formulas.end()) {
    throw exception("Unown state type");
  }
  d_transition_formulas.add_entry(id, tf);
  d_state_types_to_transition_formulas[tf->get_state_type()].insert(id);
}

void context::add_transition_formula(std::string id, std::string type_id, expr::term_ref f) {
  const state_type* st = get_state_type(type_id);
  transition_formula* tf = new transition_formula(tm(), st, f);
  add_transition_formula(id, tf);
}

const transition_formula* context::get_transition_formula(std::string id) const {
  if (!d_transition_formulas.has_entry(id)) {
    throw exception(id + " not declared");
  }
  return d_transition_formulas.get_entry(id);
}

bool context::has_transition_formula(std::string id) const {
  return d_transition_formulas.has_entry(id);
}

void context::add_transition_system(std::string id, transition_system* ts) {
  if (d_transition_systems.has_entry(id)) {
    delete ts;
    throw exception(id + " already declared");
  }
  if (d_state_types_to_transition_systems.find(ts->get_state_type()) == d_state_types_to_transition_systems.end()) {
    throw exception("Unknown state type");
  }
  d_transition_systems.add_entry(id, ts);
  d_state_types_to_transition_systems[ts->get_state_type()].insert(id);
}

const system::transition_system* context::get_transition_system(std::string id) const {
  if (!d_transition_systems.has_entry(id)) {
    throw exception(id + " not declared");
  }
  return d_transition_systems.get_entry(id);
}


bool context::has_transition_system(std::string id) const {
  return d_transition_systems.has_entry(id);
}

void context::add_assumption_to(std::string id, state_formula* sf) {
  if (!d_transition_systems.has_entry(id)) {
    throw exception(id + " not declared");
  }
  d_transition_systems.get_entry(id)->add_assumption(sf);
}


options& context::get_options() const {
  return d_options;
}

utils::statistics& context::get_statistics() const {
  return d_stats;
}

context::id_set::const_iterator context::state_formulas_begin(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_state_formulas.find(st);
  if (it == d_state_types_to_state_formulas.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.begin();
}

context::id_set::const_iterator context::state_formulas_end(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_state_formulas.find(st);
  if (it == d_state_types_to_state_formulas.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.end();
}

context::id_set::const_iterator context::transition_formulas_begin(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_transition_formulas.find(st);
  if (it == d_state_types_to_transition_formulas.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.begin();
}

context::id_set::const_iterator context::transition_formulas_end(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_transition_formulas.find(st);
  if (it == d_state_types_to_transition_formulas.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.end();
}

context::id_set::const_iterator context::transition_systems_begin(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_transition_systems.find(st);
  if (it == d_state_types_to_transition_systems.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.begin();
}

context::id_set::const_iterator context::transition_systems_end(const system::state_type* st) const {
  std::map<const state_type*, id_set>::const_iterator it = d_state_types_to_transition_systems.find(st);
  if (it == d_state_types_to_transition_systems.end()) {
    throw exception("Unknown state type.");
  }
  return it->second.end();
}


}
}
