#include "transforms.h"
#include "expand_arrays.h"
#include "remove_arrays.h"
#include "remove_subtypes.h"
#include "remove_enum_types.h"
#include "promote_nonstate_to_state.h"
#include "add_missing_next.h"
#include "inlining.h"

#include "utils/trace.h"
#include "utils/options.h"

#include <boost/program_options/options_description.hpp>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;

void preprocessor::setup_options(boost::program_options::options_description& options) {
  using namespace boost::program_options;
  options.add_options()
    ("add-missed-next", 
     "The MCMT model is extended with (next.x = state.x) if next.x is not used in the transition relation.")
    ;
}
  
preprocessor::preprocessor(system::context *ctx)
: d_ctx(ctx) {}

preprocessor::problem_t preprocessor::run_transform(transform* tr,
						    const system::transition_system* T,
						    const system::state_formula* Q){
  system::transition_system* T1 = tr->apply(T);
  system::state_formula* Q1 = tr->apply(Q);
  MSG(2) << "After "  << tr->get_name() << std::endl;
  MSG(2) << "TS: "    << *T1 << std::endl;
  MSG(2) << "QUERY: " << *Q1 << std::endl;
  return problem_t(T1,Q1);
}
  
preprocessor::problem_t preprocessor::run(std::string system_id,
					  const system::transition_system* T,
					  const system::state_formula* Q) {
  // T is registered in the context with system_id but Q might not.

  options& opts = d_ctx->get_options();
  preprocessor::problem_t r;
  static unsigned k = 0; // to generate unique id's

  // Inline functions
  std::string new_system_id(system_id + "." + std::to_string(k++)); 
  transforms::inliner i(d_ctx, new_system_id, T->get_state_type());
  r = run_transform(&i, T, Q);
  system::transition_system* T1 = r.first;
  system::state_formula* Q1 = r.second;
  
  // Remove quantifiers, array lambda terms, etc
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::expand_arrays ea(d_ctx, new_system_id);
  r = run_transform(&ea, T1, Q1);
  system::transition_system* T2 = r.first;
  system::state_formula* Q2 = r.second;

  // Remove array terms (select/write)
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_arrays ra(d_ctx, new_system_id, T2->get_state_type());
  r = run_transform(&ra, T2, Q2);
  system::transition_system* T3 = r.first;
  system::state_formula* Q3 = r.second;

  // Remove enumerate types
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_enum_types ret(d_ctx, new_system_id, T3->get_state_type());
  r = run_transform(&ret, T3, Q3);
  system::transition_system* T4 = r.first;
  system::state_formula* Q4 = r.second;

  // Remove predicate subtypes
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_subtypes rs(d_ctx, new_system_id, T4->get_state_type());
  r = run_transform(&rs, T4, Q4);
  system::transition_system* T5 = r.first;
  system::state_formula* Q5 = r.second;
  
  // JN: this transformation is needed otherwise the property can be
  // trivially false. The issue can arise when we have assumptions
  // over PARAM variables together with the fact that Yices
  // generalization method gives default values when models are not
  // fully defined. Under these circumstances, we can have some
  // constraints over some PARAM variable that contradict some given
  // default value. By promoting PARAM variables to state variables we
  // ensure that all models are fully defined so Yices' generalization
  // method does not need to assign default values.
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::promote_nonstate_to_state ps(d_ctx, new_system_id, T5->get_state_type());
  r = run_transform(&ps, T5, Q5);

  if (opts.has_option("add-missed-next")) {
    system::transition_system* T6 = r.first;
    system::state_formula* Q6 = r.second;
    new_system_id = system_id + "." + std::to_string(k++); 
    transforms::add_missing_next amn(d_ctx, new_system_id);
    r =  run_transform(&amn, T6, Q6);
  }

  return r;
}

}
}
}
