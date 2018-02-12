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
    Inline functions.
**/
  
class inliner: public transform {

  static factory::register_transform<inliner> s_register;

public:

  inliner(const system::transition_system* original)
  : transform(original), m_pImpl(0) {}

  /** Apply the transform to a state formula */
  system::state_formula* apply(const system::state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  system::transition_formula* apply(const system::transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction d);


  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formulas are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  inliner(const system::transition_system* original, system::context *ctx, std::string id, const system::state_type *st);
  
  ~inliner();

  /* Create a new transition system and state formulas without enum
     types with the given id in the constructor (to be managed by the
     context) */  
  void apply (const system::transition_system *ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Function inliner";
  }
  
  virtual size_t get_priority() const {
    return 0;
  }

private:

  // forward declaration
  class inliner_impl;
  inliner_impl *m_pImpl;
  
};
  
}
}
}
