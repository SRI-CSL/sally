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

  static factory::register_transform<remove_arrays> s_register;

public:

  remove_arrays(const system::transition_system* original)
  : transform(original) {}

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  remove_arrays(const system::transition_system* original, system::context *ctx, std::string id, const system::state_type *st);
  
  ~remove_arrays();

  /* Create a new transition system and state formulas without arrays
     (if possible) with the given id in the constructor (to be managed
     by the context) */
  void apply (const system::transition_system *ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Remove arrays";
  }

  virtual size_t get_priority() const {
    return 2;
  }

private:

  // forward declaration
  class remove_arrays_impl;
  remove_arrays_impl *m_pImpl;
  
};
  
}
}
}
