#include "assume.h"

#include <iostream>

namespace sally {
namespace cmd {

assume::assume(const system::context& ctx, std::string system_id, system::state_formula* assumption)
: command(ASSUME)
, d_system_id(system_id)
, d_assumption_state(assumption)
, d_assumption_transition(0)
{}

assume::assume(const system::context& ctx, std::string system_id, system::transition_formula* assumption)
: command(ASSUME)
, d_system_id(system_id)
, d_assumption_state(0)
, d_assumption_transition(assumption)
{}

void assume::to_stream(std::ostream& out) const  {
  if (d_assumption_state) {
    out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_assumption_state << "]";
  } else {
    assert(d_assumption_transition);
    out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_assumption_transition << "]";
  }
}

void assume::run(system::context* ctx, engine* e) {
  // Add the assumption, taken by context
  if (d_assumption_state) {
    ctx->add_assumption_to(d_system_id, d_assumption_state);
  } else {
    assert(d_assumption_transition);
    ctx->add_assumption_to(d_system_id, d_assumption_transition);
  }
  d_assumption_state = 0;
  d_assumption_transition = 0;
}

assume::~assume() {
  delete d_assumption_state;
  delete d_assumption_transition;
}

}
}
