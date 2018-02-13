#include "query.h"

#include "utils/trace.h"
#include <iostream>
#include "system/transforms/preprocessor.h"

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

  // Perform some transformations to avoid solvers complaining
  // 
  // FIXME: the preprocessor will be run on each query. Therefore, the
  // transition system will preprocessed over and over again with each
  // query. This is clearly a waste of resources.
  system::transforms::preprocessor pp(ctx, d_system_id, d_system_id + "_pp");
  std::vector<const system::state_formula*> Qs;
  Qs.push_back(d_query);  
  system::transition_system* Tf = 0;
  std::vector<const system::state_formula*> Qsf;
  pp.run(d_system_id, T, Qs, Tf, Qsf);
  assert(Qsf.size () == 1);
  const system::state_formula* Qf = Qsf[0];	

  // Check the formula
  engine::result result = e->query(Tf, Qf);
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
    const system::state_type* state_type = Tf->get_state_type();
    state_type->use_namespace();
    state_type->use_namespace(system::state_type::STATE_CURRENT);
    std::cout << "(invariant " << inv.depth << " " << inv.F << ")" << std::endl;
    ctx->tm().pop_namespace();
    ctx->tm().pop_namespace();
  }
}

query::~query() {
  delete d_query;
}

}
}
