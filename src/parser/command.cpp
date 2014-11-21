/*
 * command.cpp
 *
 *  Created on: Nov 12, 2014
 *      Author: dejan
 */

#include "parser/command.h"

#include <cassert>

using namespace sal2;
using namespace parser;

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
