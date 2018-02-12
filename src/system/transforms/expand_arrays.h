#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include "transform.h"

#include <string>

namespace sally {
namespace cmd {
namespace transforms {
  
/** 
    Expand arrays from transition systems and state formulas.  The
    expansion consists of removing quantifiers, array lambda terms and
    array variables involved in equalities. As a result of this
    expansion, all array variables should appear only as arguments of
    array read and write terms.  The expansion is only possible if the
    array size is statically known.

    Note: an array is not expanded if it appears as an argument to a
    function application term.
**/
  
class expand_arrays: public transform {

  static factory::register_transform<expand_arrays> s_register;

public:

  expand_arrays(const system::transition_system* original)
  : transform(original) {}

  /** Apply the transform to a state formula */
  system::state_formula* apply(const system::state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  system::transition_formula* apply(const system::transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction d);

  expand_arrays(const system::transition_system* original, system::context *ctx, std::string id);

  /* Create a new transition system and state formulas with the given
     id (to be managed by the context) */
  void apply (const system::transition_system *ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);

  std::string get_name() const {
    return "Expand arrays";
  }
  
  virtual size_t get_priority() const {
    return 1;
  }

private:
  
  system::context *d_ctx;
  std::string d_id;
};
  
}
}
}
