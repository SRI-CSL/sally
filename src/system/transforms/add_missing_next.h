#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include "transform.h"

#include <string>

namespace sally {
namespace system  {
namespace transforms {

/** 
    Search in the transition relation if a variable x is not updated
    and it adds an equality next.x = current.x
**/
  
class add_missing_next: public transform {

  static factory::register_transform<add_missing_next> s_register;

public:

  /** Construct the transform for the original transition system */
  add_missing_next(context* ctx, const transition_system* original);

  /** Apply the transform to a state formula */
  state_formula* apply(const state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  transition_formula* apply(const transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction D);

  add_missing_next(const transition_system* original, context *ctx, std::string id);

  /* Create a new transition system and state formulas with the given
     id (to be managed by the context) */
  void apply (const transition_system *ts,
	      const std::vector<const state_formula*>& queries,
	      transition_system*& new_ts,
	      std::vector<const state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Add missing prime variables";
  }
  
  virtual size_t get_priority() const {
    return 6;
  }

private:
  
  std::string d_id;
};
  
}
}
}
