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
    Remove array terms from transition systems and state formulas.
    This is only possible if all arrays are bounded.
**/
  
class remove_arrays: public transform {
public:

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  remove_arrays(system::context *ctx, std::string id, const system::state_type *st);
  
  ~remove_arrays();

  /* Create a new transition system without arrays (if possible) with
     the given id in the constructor (to be managed by the context) */  
  void apply (const system::transition_system *ts);
  
  /* Create a new state formula semantically equivalent to sf without
     arrays (if possible) with the given id in the constructor (to be
     managed by the context) */
  void apply(const system::state_formula *sf);

  std::string get_name() const {
    return "Remove arrays";
  }
			         
private:

  // forward declaration
  class remove_arrays_impl;
  remove_arrays_impl *m_pImpl;
  
};
  
}
}
}
