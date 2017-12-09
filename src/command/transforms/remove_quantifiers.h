#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include <string>

namespace sally {
namespace cmd {
namespace transforms {
  
/** 
    Remove quantifiers from transition systems and state formulas.
    This is only possible if all quantified variables are bounded
    (i.e., lower and upper bounds are statically known).
**/
  
class remove_quantifiers {
public:

  remove_quantifiers(system::context *ctx, std::string id);

  /* Create a new transition system without quantifiers (if possible)
     with the given id (to be managed by the context) */  
  void apply (const system::transition_system *ts);
  
  /* Create a new state formula semantically equivalent to sf without
     quantifiers (if possible) with the given id (to be managed by the
     context) */
  void apply(const system::state_formula *sf);

private:
  
  system::context *d_ctx;
  std::string d_id;
};
  
}
}
}
