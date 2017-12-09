#include "transforms.h"

#include "remove_quantifiers.h"
#include "remove_arrays.h"
#include "remove_subtypes.h"

#include "utils/trace.h"

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;

preprocessor::preprocessor(system::context *ctx)
  : d_ctx(ctx) {}

/*
  Perform following transformations:
  1) remove quantifiers, array lambda terms and array equalities, only
     if arrays are bounded.
  2) remove array write and read terms, only if arrays are bounded.
  3) remove predicate subtypes.
*/  
std::string preprocessor::run(std::string system_id, const system::transition_system* T, const system::state_formula* Q) {

  static unsigned k = 0;
  std::string new_system_id(system_id + "." + std::to_string(k++)); // must be unique
  transforms::remove_quantifiers rq(d_ctx, new_system_id);
  rq.apply(T);
  rq.apply(Q);
  const system::transition_system* T1 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q1 = d_ctx->get_state_formula(new_system_id);
  MSG(1) << "After removal of quantifiers \n";
  MSG(1) << "TS: " << *T1 << "\n";
  MSG(1) << "QUERY: " << *Q1 << "\n";
  
  new_system_id = system_id + "." + std::to_string(k++); // must be unique 
  transforms::remove_arrays ra(d_ctx, new_system_id, T1->get_state_type() /*old state type*/);
  ra.apply(T1);
  ra.apply(Q1);
  const system::transition_system* T2 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q2 = d_ctx->get_state_formula(new_system_id);
  MSG(1) << "After removal of array terms \n";
  MSG(1) << "TS: " << *T2 << "\n";
  MSG(1) << "QUERY: " << *Q2 << "\n";
  
  new_system_id = system_id + "." + std::to_string(k++); // must be unique
  transforms::remove_subtypes rs(d_ctx, new_system_id, T2->get_state_type());
  rs.apply(T2);
  rs.apply(Q2);
  const system::transition_system* T3 = d_ctx->get_transition_system(new_system_id);
  const system::state_formula* Q3 = d_ctx->get_state_formula(new_system_id);
  MSG(1) << "After removal of predicate subtypes \n";
  MSG(1) << "TS: " << *T3 << "\n";
  MSG(1) << "QUERY: " << *Q3 << "\n";

  return new_system_id;
}

}
}
}
