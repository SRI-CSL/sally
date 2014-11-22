/*
 * state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include <iostream>

#include "system/state_type.h"
#include "expr/term_manager.h"

#include <iostream>

namespace sal2 {
namespace system {

state_type::state_type(expr::term_manager& tm, std::string id, expr::term_ref type)
: d_id(id)
, d_type(tm, type)
{
  d_current_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(CURRENT), type));
  d_next_state = expr::term_ref_strong(tm, tm.mk_variable(id + "::" + to_string(NEXT), type));
}

void state_type::use_namespace(expr::term_manager& tm) const {
  tm.use_namespace(d_id + "::");
}

void state_type::use_namespace(expr::term_manager& tm, var_class vc) const {
  tm.use_namespace(to_string(vc) + ".");
}

void state_type::to_stream(std::ostream& out) const {
  out << "[" << d_id << ": " << d_type << "]";
}

expr::term_ref state_type::get_state(var_class vc) const {
  switch (vc) {
  case CURRENT:
    return d_current_state;
  case NEXT:
    return d_next_state;
  }
  assert(false);
  return expr::term_ref();
}

std::string state_type::to_string(var_class vc) {
  switch (vc) {
  case CURRENT:
    return "state";
  case NEXT:
    return "next";
  }
  assert(false);
  return "unknown";
}

std::ostream& operator << (std::ostream& out, const state_type& st) {
  st.to_stream(out);
  return out;
}

}
}
