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
    Remove predicate subtypes from transition systems and state formulas.
**/
  
class remove_subtypes: public transform {

  static factory::register_transform s_register;

public:

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  remove_subtypes(system::context *ctx, std::string id, const system::state_type *st);
  
  ~remove_subtypes();

  /* Create a new transition system and state formulas without
     predicate subtypes with the given id in the constructor (to be
     managed by the context) */
  void apply (const system::transition_system *ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Remove predicate subtypes";
  }
  
  virtual size_t get_priority() const {
    return 4;
  }

private:

  // forward declaration
  class remove_subtypes_impl;
  remove_subtypes_impl *m_pImpl;
  
};
  
}
}
}
