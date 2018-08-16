#include "define_states.h"

#include <iostream>

namespace sally {
namespace cmd {

define_states::define_states(std::string id, system::state_formula* formula)
: command(DEFINE_STATES)
, d_id(id)
, d_formula(formula)
{}

void define_states::run(system::context* ctx, engine* e) {
  ctx->add_state_formula(d_id, d_formula);
  d_formula = 0;
}

define_states::~define_states() {
  delete d_formula;
}
void define_states::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << "(" << d_id << "): ";
  out << *d_formula;
  out << "]";
}

}
}
