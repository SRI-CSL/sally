#include "expand_arrays.h"
#include "remove_arrays.h"
#include "remove_subtypes.h"
#include "remove_enum_types.h"
#include "add_missing_next.h"
#include "inlining.h"

#include "utils/trace.h"
#include "utils/options.h"

#include <boost/program_options/options_description.hpp>
#include "preprocessor.h"
#include "promote_params_to_state.h"

namespace sally {
namespace system {
namespace transforms {

using namespace expr;

void preprocessor::setup_options(boost::program_options::options_description& options) {
  std::string default_transforms = factory::get_default_transforms_list();

  std::stringstream available_transforms;
  available_transforms << "List separated transforms. Available: " << factory::get_transforms_list();

  using namespace boost::program_options;
  options.add_options()
    ("add-missed-next", "Extend the model is with (next.x = state.x) if next.x is not used.")
    ("preprocessor-transforms",
        boost::program_options::value<std::string>()->default_value(default_transforms),
        available_transforms.str().c_str())
  ;
}
  
preprocessor::preprocessor(context *ctx, std::string system_id, std::string preprocessed_id)
: d_ctx(ctx)
, d_original(ctx->get_transition_system(system_id))
{
  // Remove for now
  if (false) {
    std::vector<std::string> transforms;

    // Get the list of transforms from comma separated option
    std::string transforms_list = ctx->get_options().get_string("preprocessor-transforms");
    size_t start = 0, find = std::string::npos;
    std::string transform_name;
    while ((find = transforms_list.find(',', start)) != std::string::npos) {
      transform_name = transforms_list.substr(start, find - start);
      transforms.push_back(transform_name);
      start = find + 1;
    }
    transform_name = transforms_list.substr(start);
    transforms.push_back(transform_name);

    // Allocate the transforms
    const transition_system* current_system = d_original;
    for (size_t i = 0; i < transforms.size(); ++ i) {
      transform* current_transform = factory::mk_transform(transforms[i], ctx, current_system);
      d_transforms.push_back(current_transform);
      current_system = current_transform->get_transformed();
    }
  }
}

preprocessor::~preprocessor() {
  for (size_t i = 0; i < d_transforms.size(); ++ i) {
    delete d_transforms[i];
  }
}

state_formula* preprocessor::apply(const state_formula* sf, transform::direction D) {
  const state_formula* current = sf;
  state_formula* next = 0;
  switch (D) {
  case transform::TRANSFORM_FORWARD:
    for (transforms_vector::iterator it = d_transforms.begin(); it != d_transforms.end(); ++ it) {
      next = (*it)->apply(current, D);
      if (current != sf) { delete current; }
      current = next;
    }
    break;
  case transform::TRANSFORM_BACKWARD:
    for (transforms_vector::reverse_iterator it = d_transforms.rbegin(); it != d_transforms.rend(); ++ it) {
      next = (*it)->apply(current, D);
      if (current != sf) { delete current; }
      current = next;
    }
    break;
  }
  // Return the last one transformed
  return next;
}

transition_formula* preprocessor::apply(const transition_formula* tf, transform::direction D) {
  const transition_formula* current = tf;
  transition_formula* next = 0;
  switch (D) {
  case transform::TRANSFORM_FORWARD:
    for (transforms_vector::iterator it = d_transforms.begin(); it != d_transforms.end(); ++ it) {
      next = (*it)->apply(current, D);
      if (current != tf) { delete current; }
      current = next;
    }
    break;
  case transform::TRANSFORM_BACKWARD:
    for (transforms_vector::reverse_iterator it = d_transforms.rbegin(); it != d_transforms.rend(); ++ it) {
      next = (*it)->apply(current, D);
      if (current != tf) { delete current; }
      current = next;
    }
    break;
  }
  // Return the last one transformed
  return next;
}

expr::model::ref preprocessor::apply(expr::model::ref m, transform::direction D) {
  expr::model::ref current = m;
  expr::model::ref next;
  switch (D) {
  case transform::TRANSFORM_FORWARD:
    for (transforms_vector::iterator it = d_transforms.begin(); it != d_transforms.end(); ++ it) {
      next = (*it)->apply(current, D);
      current = next;
    }
    break;
  case transform::TRANSFORM_BACKWARD:
    for (transforms_vector::reverse_iterator it = d_transforms.rbegin(); it != d_transforms.rend(); ++ it) {
      next = (*it)->apply(current, D);
      current = next;
    }
    break;
  }
  // Return the last one transformed
  return next;
}

void preprocessor::run_transform(transform* tr,
				 const transition_system* ts,
				 const std::vector<const state_formula*>& queries,
				 transition_system*& new_ts,
				 std::vector<const state_formula*>& new_queries) {
  
  tr->apply(ts, queries, new_ts, new_queries);
  MSG(2) << "After "  << tr->get_name() << std::endl;
  MSG(2) << "TS: "    << *new_ts << std::endl;
  MSG(2) << "QUERIES: \n";
  for (std::vector<const state_formula*>::iterator it = new_queries.begin(),
	 et = new_queries.end(); it!=et; ++it) {
    MSG(2) << "\t" << *(*it) << std::endl;
  }
}
  
std::string make_id(std::string prefix) {
  static unsigned k = 0; // to generate unique id's
  std::stringstream system_id_ss;
  system_id_ss << prefix << "." << k ++;
  return system_id_ss.str();
}

void preprocessor::run(std::string system_id,
		       const transition_system* T,
		       const std::vector<const state_formula*>& Qs,
		       transition_system*& newT,
		       std::vector<const state_formula*>& newQs) {
  
  // T is registered in the context with system_id but Qs might not.

  options& opts = d_ctx->get_options();


  // Inline functions
  transforms::inliner i(T, d_ctx, make_id(system_id), T->get_state_type());
  transition_system* T1 = 0;
  std::vector<const state_formula*> Qs1;
  run_transform(&i, T, Qs, T1, Qs1);
  MSG(1) << "Inlined functions." << std::endl;
  // Remove quantifiers, array lambda terms, etc
  transforms::expand_arrays ea(i.get_transformed(), d_ctx, make_id(system_id));
  transition_system* T2 = 0;
  std::vector<const state_formula*> Qs2;
  run_transform(&ea, T1, Qs1, T2, Qs2);
  MSG(1) << "Removed quantifiers and array lambda terms." << std::endl;  
  // Remove array terms (select/write)
  transforms::remove_arrays ra(ea.get_transformed(), d_ctx, make_id(system_id), T2->get_state_type());
  transition_system* T3 = 0;
  std::vector<const state_formula*> Qs3;
  run_transform(&ra, T2, Qs2, T3, Qs3);
  MSG(1) << "Removed array terms." << std::endl;    
  // Remove enumerate types
  transforms::remove_enum_types ret(ra.get_transformed(), d_ctx, make_id(system_id), T3->get_state_type());
  transition_system* T4 = 0;
  std::vector<const state_formula*> Qs4;
  run_transform(&ret, T3, Qs3, T4, Qs4);
  MSG(1) << "Removed enumerate types." << std::endl;        
  // Remove predicate subtypes
  transforms::remove_subtypes rs(ret.get_transformed(), d_ctx, make_id(system_id), T4->get_state_type());
  transition_system* T5 = 0;
  std::vector<const state_formula*> Qs5;
  run_transform(&rs, T4, Qs4, T5, Qs5);
  MSG(1) << "Removed predicate subtypes." << std::endl;      
  // JN: this transformation is needed otherwise the property can be
  // trivially false. The issue can arise when we have assumptions
  // over PARAM variables together with the fact that Yices
  // generalization method gives default values when models are not
  // fully defined. Under these circumstances, we can have some
  // constraints over some PARAM variable that contradict some given
  // default value. By promoting PARAM variables to state variables we
  // ensure that all models are fully defined so Yices' generalization
  // method does not need to assign default values.
  transforms::promote_params_to_state ps(rs.get_transformed(), d_ctx, make_id(system_id), T5->get_state_type());
  transition_system* T6 = 0;
  std::vector<const state_formula*> Qs6;
  run_transform(&ps, T5, Qs5, T6, Qs6);
  MSG(1) << "Promoted all PARAM variables to state ones." << std::endl;
  
  if (opts.has_option("add-missed-next")) {
    transforms::add_missing_next amn(ps.get_transformed(), d_ctx, make_id(system_id));
    run_transform(&amn, T6, Qs6, newT, newQs);
    MSG(1) << "Added x' = x for any unused current x variable." << std::endl;    
  } else {
    newT = T6;
    newQs = Qs6;
  }
  
}

}
}
}
