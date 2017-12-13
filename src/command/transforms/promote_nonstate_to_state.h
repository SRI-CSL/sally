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
    Promote non-state to state variables.
**/
  
class promote_nonstate_to_state: public transform {
public:

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  promote_nonstate_to_state(system::context *ctx, std::string id, const system::state_type *st);
  
  ~promote_nonstate_to_state();

  /* Create a new transition system with the given id in the
     constructor (to be managed by the context) */  
  system::transition_system* apply (const system::transition_system *ts);

  /* Create a new state formula with the given id in the constructor
     (to be managed by the context) */    
  system::state_formula* apply(const system::state_formula *sf);

  std::string get_name() const {
    return "Promote non-state to state variables";
  }
  
private:

  // forward declaration
  class promote_nonstate_to_state_impl;
  promote_nonstate_to_state_impl *m_pImpl;
  
};
  
}
}
}
