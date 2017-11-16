#include "query.h"

#include "utils/trace.h"
#include "transforms/remove_quantifiers.h"

#include <iostream>

namespace sally {
namespace cmd {

query::query(const system::context& ctx, std::string system_id, system::state_formula* sf)
: command(QUERY)
, d_system_id(system_id)
, d_query(sf)
{}

void query::to_stream(std::ostream& out) const  {
  // XXX: this prints the query before any transformation
  out << "[" << get_command_type_string() << " " << d_system_id << " " << *d_query << "]";
}

void query::run(system::context* ctx, engine* e) {
  // If in parse only mode, we're done
  if (ctx->get_options().has_option("parse-only")) { return; }
  // We need an engine
  if (e == 0) { throw exception("Engine needed to do a query."); }
  // Get the transition system
  const system::transition_system* T = ctx->get_transition_system(d_system_id);

  /* Begin transformations */
  transforms::remove_quantifiers rq (ctx);
  const system::transition_system* T1 = rq.apply(T);
  const system::state_formula * Q1 = rq.apply(d_query);

  MSG(1) << "After removal of quantifiers \n";
  MSG(1) << *T1 << "\n";
  MSG(1) << *Q1 << "\n";  
  
  /* End transformations */
  
  // Check the formula
  engine::result result = e->query(T1, Q1);
  // Output the result if not silent
  if (result != engine::SILENT) {
    std::cout << result << std::endl;
  }
  // If invalid, and asked to, show the trace
  if (result == engine::INVALID && ctx->get_options().has_option("show-trace")) {
    const system::trace_helper* trace = e->get_trace();
    std::cout << *trace << std::endl;
  }
  // If valid, and asked to, show the invariant
  if (result == engine::VALID && ctx->get_options().has_option("show-invariant")) {
    engine::invariant inv = e->get_invariant();
    const system::state_type* state_type = T1->get_state_type();
    state_type->use_namespace();
    state_type->use_namespace(system::state_type::STATE_CURRENT);
    std::cout << "(invariant " << inv.depth << " " << inv.F << ")" << std::endl;
    ctx->tm().pop_namespace();
    ctx->tm().pop_namespace();
  }

  // FIXME: remove quantifiers should own the pointers
  delete T1;
  delete Q1;
}

query::~query() {
  delete d_query;
}

}
}
