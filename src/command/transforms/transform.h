#pragma once

#include "system/state_formula.h"
#include "system/transition_system.h"

#include <string>
#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

class transform {
public:
  
  virtual ~transform() {}

  virtual void apply (const system::transition_system *ts,
		      const std::vector<const system::state_formula*>& queries,
		      system::transition_system*& new_ts,
		      std::vector<const system::state_formula*>& new_queries) = 0;
  
  virtual std::string get_name() const = 0;
};
}
}
}
