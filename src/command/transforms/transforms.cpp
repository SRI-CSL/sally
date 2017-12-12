#include "transforms.h"

#include "expand_arrays.h"
#include "remove_arrays.h"
#include "remove_subtypes.h"
#include "remove_enum_types.h"

#include "utils/trace.h"

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;

preprocessor::preprocessor(system::context *ctx)
  : d_ctx(ctx) {}

std::string preprocessor::run(std::string system_id,
			      const system::transition_system* T, const system::state_formula* Q) {

  static unsigned k = 0;
  
  std::string new_system_id(system_id + "." + std::to_string(k++)); // must be unique
  transforms::expand_arrays ea(d_ctx, new_system_id);
  ea.apply(T);
  ea.apply(Q);
  const system::transition_system* T1 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q1 = d_ctx->get_state_formula(new_system_id);
  MSG(2) << "After "  << ea.get_name() << std::endl;
  MSG(2) << "TS: "    << *T1 << std::endl;
  MSG(2) << "QUERY: " << *Q1 << std::endl;
  
  new_system_id = system_id + "." + std::to_string(k++); // must be unique 
  transforms::remove_arrays ra(d_ctx, new_system_id, T1->get_state_type());
  ra.apply(T1);
  ra.apply(Q1);
  const system::transition_system* T2 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q2 = d_ctx->get_state_formula(new_system_id);
  MSG(2) << "After "  << ra.get_name() << std::endl;
  MSG(2) << "TS: "    << *T2 << std::endl;
  MSG(2) << "QUERY: " << *Q2 << std::endl;
  
  new_system_id = system_id + "." + std::to_string(k++); // must be unique
  transforms::remove_enum_types ret(d_ctx, new_system_id, T2->get_state_type());
  ret.apply(T2);
  ret.apply(Q2);
  const system::transition_system* T3 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q3 = d_ctx->get_state_formula(new_system_id);
  MSG(2) << "After "  << ret.get_name() << std::endl;
  MSG(2) << "TS: "    << *T3 << std::endl;
  MSG(2) << "QUERY: " << *Q3 << std::endl;
  
  new_system_id = system_id + "." + std::to_string(k++); // must be unique
  transforms::remove_subtypes rs(d_ctx, new_system_id, T3->get_state_type());
  rs.apply(T3);
  rs.apply(Q3);
  const system::transition_system* T4 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q4 = d_ctx->get_state_formula(new_system_id);
  MSG(2) << "After "  << rs.get_name() << std::endl;
  MSG(2) << "TS: "    << *T4 << std::endl;
  MSG(2) << "QUERY: " << *Q4 << std::endl;

  return new_system_id;
}

}
}
}
