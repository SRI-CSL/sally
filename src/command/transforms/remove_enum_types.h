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
    Remove enum types from transition systems and state formulas.
**/
  
class remove_enum_types: public transform {
public:

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  remove_enum_types(system::context *ctx, std::string id, const system::state_type *st);
  
  ~remove_enum_types();

  /* Create a new transition system without enum types with
     the given id in the constructor (to be managed by the context) */  
  void apply (const system::transition_system *ts);
  
  /* Create a new state formula semantically equivalent to sf without
     enum types with the given id in the constructor (to be managed by
     the context) */
  void apply(const system::state_formula *sf);

  std::string get_name() const {
    return "Remove enumeration types";
  }
  
private:

  // forward declaration
  class remove_enum_types_impl;
  remove_enum_types_impl *m_pImpl;
  
};
  
}
}
}
