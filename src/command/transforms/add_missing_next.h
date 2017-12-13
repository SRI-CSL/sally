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
    Search in the transition relation if a variable x is not updated
    and it adds an equality next.x = current.x
**/
  
class add_missing_next: public transform {
public:

  add_missing_next(system::context *ctx, std::string id);

  /* Create a new transition system with the given id (to be managed
     by the context) */  
  system::transition_system* apply (const system::transition_system *ts);
  
  /* Create a new state formula with the given id (to be managed by
     the context) */
  system::state_formula* apply(const system::state_formula *sf);

  std::string get_name() const {
    return "Add missing prime variables";
  }
  
private:
  
  system::context *d_ctx;
  std::string d_id;
};
  
}
}
}
