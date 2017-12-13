#include "transforms.h"

#include "expand_arrays.h"
#include "remove_arrays.h"
#include "remove_subtypes.h"
#include "remove_enum_types.h"
#include "promote_nonstate_to_state.h"

#include "utils/trace.h"

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;

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
  // T is registered in system_id but Q might not.
  static unsigned k = 0; // to generate unique id's

  /* Then next four transformations must be done in this order */
  std::string new_system_id(system_id + "." + std::to_string(k++)); 
  transforms::expand_arrays ea(d_ctx, new_system_id);
  preprocessor::problem_t r1 = run_transform(&ea, T, Q);
  system::transition_system* T1 = r1.first;
  system::state_formula* Q1 = r1.second;
  
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_arrays ra(d_ctx, new_system_id, T1->get_state_type());
  preprocessor::problem_t r2 = run_transform(&ra, T1, Q1);
  system::transition_system* T2 = r2.first;
  system::state_formula* Q2 = r2.second;

  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_enum_types ret(d_ctx, new_system_id, T2->get_state_type());
  preprocessor::problem_t r3 = run_transform(&ret, T2, Q2);
  system::transition_system* T3 = r3.first;
  system::state_formula* Q3 = r3.second;

  
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_subtypes rs(d_ctx, new_system_id, T3->get_state_type());
  preprocessor::problem_t r4 = run_transform(&rs, T3, Q3);
  system::transition_system* T4 = r4.first;
  system::state_formula* Q4 = r4.second;
  
  /* this transformation can be done at anytime */

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
  transforms::promote_nonstate_to_state ps(d_ctx, new_system_id, T4->get_state_type());
  preprocessor::problem_t r5 =  run_transform(&ps, T4, Q4);
    
  return r5;
}

}
}
}
