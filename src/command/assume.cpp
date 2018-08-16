#include "assume.h"

#include <iostream>

namespace sally {
namespace cmd {

assume::assume(const system::context& ctx, std::string system_id, system::state_formula* assumption)
: command(ASSUME)
, d_system_id(system_id)
, d_assumption(assumption)
{}

void assume::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_assumption << "]";
}

void assume::run(system::context* ctx, engine* e) {
  // Add the assumption
  ctx->add_assumption_to(d_system_id, d_assumption);
  // Taken by the context
  d_assumption = 0;
}

assume::~assume() {
  delete d_assumption;
}

}
}
