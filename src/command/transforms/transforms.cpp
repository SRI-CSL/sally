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

void preprocessor::run_transform(transform* tr,
				 const system::transition_system* ts,
				 const std::vector<const system::state_formula*>& queries,
				 system::transition_system*& new_ts,
				 std::vector<const system::state_formula*>& new_queries) {
  
  tr->apply(ts, queries, new_ts, new_queries);
  MSG(2) << "After "  << tr->get_name() << std::endl;
  MSG(2) << "TS: "    << *new_ts << std::endl;
  MSG(2) << "QUERIES: \n";
  for (std::vector<const system::state_formula*>::iterator it = new_queries.begin(),
	 et = new_queries.end(); it!=et; ++it) {
    MSG(2) << "\t" << *it << std::endl;
  }
}
  
void preprocessor::run(std::string system_id,
		       const system::transition_system* T,
		       const std::vector<const system::state_formula*>& Qs,
		       system::transition_system*& newT,
		       std::vector<const system::state_formula*>& newQs) {
  
  // T is registered in the context with system_id but Qs might not.

  options& opts = d_ctx->get_options();
  static unsigned k = 0; // to generate unique id's

  // Inline functions
  std::string new_system_id(system_id + "." + std::to_string(k++)); 
  transforms::inliner i(d_ctx, new_system_id, T->get_state_type());
  system::transition_system* T1 = nullptr;
  std::vector<const system::state_formula*> Qs1;  
  run_transform(&i, T, Qs, T1, Qs1);
  // Remove quantifiers, array lambda terms, etc
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::expand_arrays ea(d_ctx, new_system_id);
  system::transition_system* T2 = nullptr;
  std::vector<const system::state_formula*> Qs2;    
  run_transform(&ea, T1, Qs1, T2, Qs2);
  // Remove array terms (select/write)
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_arrays ra(d_ctx, new_system_id, T2->get_state_type());
  system::transition_system* T3 = nullptr;
  std::vector<const system::state_formula*> Qs3;    
  run_transform(&ra, T2, Qs2, T3, Qs3);
  // Remove enumerate types
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_enum_types ret(d_ctx, new_system_id, T3->get_state_type());
  system::transition_system* T4 = nullptr;
  std::vector<const system::state_formula*> Qs4;    
  run_transform(&ret, T3, Qs3, T4, Qs4);
  // Remove predicate subtypes
  new_system_id = system_id + "." + std::to_string(k++); 
  transforms::remove_subtypes rs(d_ctx, new_system_id, T4->get_state_type());
  system::transition_system* T5 = nullptr;
  std::vector<const system::state_formula*> Qs5;   
  run_transform(&rs, T4, Qs4, T5, Qs5);
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
  system::transition_system* T6 = nullptr;
  std::vector<const system::state_formula*> Qs6;    
  run_transform(&ps, T5, Qs5, T6, Qs6);

  if (opts.has_option("add-missed-next")) {
    new_system_id = system_id + "." + std::to_string(k++); 
    transforms::add_missing_next amn(d_ctx, new_system_id);
    run_transform(&amn, T6, Qs6, newT, newQs);
  } else {
    newT = T6;
    newQs = Qs6;
  }
  
}

}
}
}
