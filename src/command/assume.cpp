#include "assume.h"

#include <iostream>

namespace sally {
namespace cmd {

assume_command::assume_command(const system::context& ctx, std::string system_id, system::state_formula* assumption)
: command(ASSUME)
, d_system_id(system_id)
, d_assumption(assumption)
{}

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

}
}
