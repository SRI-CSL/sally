#include "query.h"

#include <iostream>

namespace sally {
namespace cmd {

query_command::query_command(const system::context& ctx, std::string system_id, system::state_formula* sf)
: command(QUERY)
, d_system_id(system_id)
, d_query(sf)
{}

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

}
}
