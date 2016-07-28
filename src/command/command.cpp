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

#include "command.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace cmd {

command::command(command::type t)
: d_type(t)
{}

std::string command::get_command_type_string() const {

#define CASE_TO_STRING(TYPE) case TYPE: return #TYPE; break;
switch (d_type) {
  CASE_TO_STRING(SEQUENCE)
  CASE_TO_STRING(DECLARE_STATE_TYPE)
  CASE_TO_STRING(DEFINE_STATES)
  CASE_TO_STRING(DEFINE_TRANSITION)
  CASE_TO_STRING(DEFINE_TRANSITION_SYSTEM)
  CASE_TO_STRING(ASSUME)
  CASE_TO_STRING(QUERY)
default:
  assert(false);
}

return "unknown";

#undef CASE_TO_STRING
}

void declare_state_type_command::run(system::context* ctx, engine* e) {
  ctx->add_state_type(d_id, d_state_type);
  d_state_type = 0;
}

declare_state_type_command::~declare_state_type_command() {
  delete d_state_type;
}

void declare_state_type_command::to_stream(std::ostream& out) const {
  out << "[" << get_command_type_string() << "(" << d_id << "): ";
  out << *d_state_type;
  out << "]";
}

void define_states_command::run(system::context* ctx, engine* e) {
  ctx->add_state_formula(d_id, d_formula);
  d_formula = 0;
}

define_states_command::~define_states_command() {
  delete d_formula;
}
void define_states_command::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << "(" << d_id << "): ";
  out << *d_formula;
  out << "]";
}

void define_transition_command::run(system::context* ctx, engine* e) {
  ctx->add_transition_formula(d_id, d_formula);
  d_formula = 0;
}

define_transition_command::~define_transition_command() {
  delete d_formula;
}

void define_transition_command::to_stream(std::ostream& out) const {
  out << "[" << get_command_type_string() << "(" << d_id << "): ";
  out << *d_formula;
  out << "]";
}

define_transition_command::define_transition_command(std::string id, system::transition_formula* formula)
: command(DEFINE_TRANSITION)
, d_id(id)
, d_formula(formula)
{
}

void define_transition_system_command::run(system::context* ctx, engine* e) {
  ctx->add_transition_system(d_id, d_system);
  d_system = 0;
}

define_transition_system_command::~define_transition_system_command() {
  delete d_system;
}

void define_transition_system_command::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << "(" << d_id << "): ";
  out << *d_system;
  out << "]";
}

void query_command::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_query << "]";
}

void query_command::run(system::context* ctx, engine* e) {
  // If in parse only mode, we're done
  if (ctx->get_options().has_option("parse-only")) { return; }
  // We need an engine
  if (e == 0) { throw exception("Engine needed to do a query."); }
  // Get the transition system
  const system::transition_system* T = ctx->get_transition_system(d_system_id);
  // Check the formula
  engine::result result = e->query(T, d_query);
  // Output the result if not silent
  if (result != engine::SILENT) {
    std::cout << result << std::endl;
  }
  // If invalid, and asked to, show the trace
  if (result == engine::INVALID && ctx->get_options().has_option("show-trace")) {
    const system::trace_helper* trace = e->get_trace();
    std::cout << *trace << std::endl;
  }
}

query_command::~query_command() {
  delete d_query;
}

void assume_command::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_assumption << "]";
}

void assume_command::run(system::context* ctx, engine* e) {
  // Add the assumption
  ctx->add_assumption_to(d_system_id, d_assumption);
  // Taken by the context
  d_assumption = 0;
}

assume_command::~assume_command() {
  delete d_assumption;
}


sequence_command::~sequence_command() {
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    delete d_commands[i];
  }
}

void sequence_command::push_back(command* command) {
  d_commands.push_back(command);
}

size_t sequence_command::size() const {
  return d_commands.size();
}

command* sequence_command::operator [] (size_t i) const {
  return d_commands[i];
}

void sequence_command::run(system::context* ctx, engine* e) {
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    d_commands[i]->run(ctx, e);
  }
}

void sequence_command::to_stream(std::ostream& out) const {
  out << "[" << get_command_type_string();
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    out << std::endl << *d_commands[i] << std::endl;
  }
  out << "]";
}

std::ostream& operator << (std::ostream& out, const command& cmd) {
  cmd.to_stream(out);
  return out;
}

}
}
