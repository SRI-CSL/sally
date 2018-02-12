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

  static factory::register_transform s_register;

public:

  add_missing_next(system::context *ctx, std::string id);

  add_missing_next(system::context *ctx, std::string id);

  /* Create a new transition system and state formulas with the given
     id (to be managed by the context) */
  void apply (const system::transition_system *ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Add missing prime variables";
  }
  
  virtual size_t get_priority() const {
    return 6;
  }

private:
  
  system::context *d_ctx;
  std::string d_id;
};
  
}
}
}
