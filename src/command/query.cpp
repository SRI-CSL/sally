#include "query.h"

#include <iostream>

namespace sally {
namespace cmd {

query::query(const system::context& ctx, std::string system_id, system::state_formula* q)
: command(QUERY)
, d_system_id(system_id)
{
  d_queries.push_back(q);
}

query::query(const system::context& ctx, std::string system_id, const std::vector<system::state_formula*>& queries)
: command(QUERY)
, d_system_id(system_id)
, d_queries(queries)
{}

void query::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << d_system_id << " ";
  for (size_t i = 0; i < d_queries.size(); ++ i) {
    if (i) out << " ";
    out << *d_queries[i];
  }
  out << "]";
}

void query::run(system::context* ctx, engine* e) {
  // If in parse only mode, we're done
  if (ctx->get_options().has_option("parse-only")) { return; }
  // We need an engine
  if (e == 0) { throw exception("Engine needed to do a query."); }
  // Get the transition system
  const system::transition_system* T = ctx->get_transition_system(d_system_id);
  // Check the formula
  for (size_t i = 0; i < d_queries.size(); ++ i) {
    engine::result result = e->query(T, d_queries[i]);
    // Output the result if not silent and stats-format is not set
    if (result != engine::SILENT && result != engine::SILENT_WITH_TRACE && !ctx->get_options().has_option("stats-format")) {
      std::cout << result << std::endl;
    }
    // If invalid, and asked to, show the trace
    if ((result == engine::INVALID || result == engine::SILENT_WITH_TRACE) && ctx->get_options().has_option("show-trace")) {
      const system::trace_helper* trace = e->get_trace();
      std::cout << *trace << std::endl;
    }
    // If valid, and asked to, show the invariant
    if (result == engine::VALID && ctx->get_options().has_option("show-invariant")) {
      engine::invariant inv = e->get_invariant();
      const system::state_type* state_type = T->get_state_type();
      state_type->use_namespace();
      state_type->use_namespace(system::state_type::STATE_CURRENT);
      std::cout << "(invariant " << inv.depth << " " << inv.F << ")" << std::endl;
      ctx->tm().pop_namespace();
      ctx->tm().pop_namespace();
    }
  }
}

query::~query() {
  for (size_t i = 0; i < d_queries.size(); ++ i) {
    delete d_queries[i];
  }
}

}
}
