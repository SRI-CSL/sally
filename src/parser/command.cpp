/*
 * command.cpp
 *
 *  Created on: Nov 12, 2014
 *      Author: dejan
 */

#include "parser/command.h"

#include <cassert>
#include <iostream>

namespace sal2 {
namespace parser {

command::command(command::type t)
: d_type(t)
{}

std::string command::get_command_type_string() const {

#define CASE_TO_STRING(TYPE) case TYPE: return #TYPE; break;
switch (d_type) {
  CASE_TO_STRING(DECLARE_STATE_TYPE)
  CASE_TO_STRING(DEFINE_STATES)
  CASE_TO_STRING(DEFINE_TRANSITION)
  CASE_TO_STRING(DEFINE_TRANSITION_SYSTEM)
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
  engine::result result = e->query(*T, d_query);
  std::cout << result << std::endl;
  // If invalid, and asked to, show the trace
  if (result == engine::INVALID && ctx->get_options().has_option("show-trace")) {
    const system::state_trace* trace = e->get_trace();
    std::cout << *trace << std::endl;
  }
}

query_command::~query_command() {
  delete d_query;
}

std::ostream& operator << (std::ostream& out, const command& cmd) {
  cmd.to_stream(out);
  return out;
}

}
}
