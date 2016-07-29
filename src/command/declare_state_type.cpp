#include "declare_state_type.h"

#include <iostream>

namespace sally {
namespace cmd {

declare_state_type_command::declare_state_type_command(std::string state_id, system::state_type* state_type)
: command(DECLARE_STATE_TYPE)
, d_id(state_id)
, d_state_type(state_type)
{}

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

}
}

