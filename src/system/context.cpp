/*
 * context.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "system/context.h"

namespace sal2 {
namespace system {

context::context(expr::term_manager& tm)
: d_term_manager(tm)
, d_state_types("state types")
, d_state_formulas("state formulas")
, d_transition_formulas("state transition formulas")
, d_transition_systems("state transition systems")
{
}

void context::add_state_type(std::string id, state_type* st) {
  if (d_state_types.has_entry(id)) {
    delete st; // Context owns it, so delete it
    throw context_exception(id + " already declared");
  }
  d_state_types.add_entry(id, st);
}

const state_type* context::get_state_type(std::string id) const {
  if (!d_state_types.has_entry(id)) {
    throw context_exception(id + " not declared");
  }
  return d_state_types.get_entry(id);
}

bool context::has_state_type(std::string id) const {
  return d_state_types.has_entry(id);
}

void context::add_state_formula(std::string id, state_formula* sf) {
  if (d_state_formulas.has_entry(id)) {
    delete sf; // Context owns it, so delete it
    throw context_exception(id + "already declared");
  }
  return d_state_formulas.add_entry(id, sf);
}

const state_formula* context::get_state_formula(std::string id) const {
  if (!d_state_formulas.has_entry(id)) {
    throw context_exception(id + " not declered");
  }
  return d_state_formulas.get_entry(id);
}

bool context::has_state_formula(std::string id) const {
  return d_state_formulas.has_entry(id);
}

void context::add_transition_formula(std::string id, transition_formula* tf) {
  if (d_transition_formulas.has_entry(id)) {
    delete tf;
    throw context_exception(id + " already declared");
  }
  d_transition_formulas.add_entry(id, tf);
}

const transition_formula* context::get_transition_formula(std::string id) const {
  if (!d_transition_formulas.has_entry(id)) {
    throw context_exception(id + " not declared");
  }
  return d_transition_formulas.get_entry(id);
}

bool context::has_transition_formula(std::string id) const {
  return d_transition_formulas.has_entry(id);
}

void context::add_transition_system(std::string id, transition_system* ts) {
  if (d_transition_systems.has_entry(id)) {
    delete ts;
    throw context_exception(id + " already declared");
  }
  d_transition_systems.add_entry(id, ts);
}

const system::transition_system* context::get_transition_system(std::string id) const {
  if (!d_transition_systems.has_entry(id)) {
    throw context_exception(id + " not declared");
  }
  return d_transition_systems.get_entry(id);
}

bool context::has_transition_system(std::string id) const {
  return d_transition_systems.has_entry(id);
}

}
}

