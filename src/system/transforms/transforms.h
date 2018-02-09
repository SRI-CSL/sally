#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "transform.h"

#include <boost/program_options/options_description.hpp>

#include <string>
#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

/**
 * Transformations to simplify the syntax of the transitions system
 * and state formulas so that solvers can handle them.
**/
class preprocessor {
public:
  
  preprocessor(system::context* ctx);
  
  /**
     Perform several transformations on the given ts and queries.  The
     transformation is functional so it produces a new transition
     system and a new vector of queries.
  **/
  void run(std::string id,
	   const system::transition_system* ts,
	   const std::vector<const system::state_formula*>& queries,
	   system::transition_system*& new_ts,
	   std::vector<const system::state_formula*>& new_queries);

  static void setup_options(boost::program_options::options_description& options);
  
private:
  
  system::context* d_ctx;
  
  void run_transform(transform* tr,
		     const system::transition_system* ts,
		     const std::vector<const system::state_formula*>& queries,
		     system::transition_system*& new_ts,
		     std::vector<const system::state_formula*>& new_queries);
};
}
}
}
