#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "transform.h"

#include <boost/program_options/options_description.hpp>

#include <string>

namespace sally {
namespace cmd {
namespace transforms {

/**
 * Transformations to simplify the syntax of the transitions system
 * and state formulas so that solvers can handle them.
**/
class preprocessor {
public:
  
  typedef std::pair<system::transition_system*, system::state_formula*> problem_t;
  
  preprocessor(system::context* ctx);
  
  /** JN: this current API performs transformation on each pair
      transition system-query. This the case for the query
      command. This is very inneficient with multiple queries because
      it will transform the same transition system multiple times.
      Ideally, we would like to modify the context by replacing all
      the transition systems, formulas, etc associated with each id by
      their transformed versions. However, this requires to change the
      current API of the context class.
  **/
  
  /**
     Perform several transformations on the given T and Q.  The
     transformation is functional so it produces a new T and a new Q.
  **/
  problem_t run(std::string id, const system::transition_system* T, const system::state_formula* Q);

  static void setup_options(boost::program_options::options_description& options);
  
private:
  
  system::context* d_ctx;
  
  problem_t run_transform(transform* tr, const system::transition_system* T, const system::state_formula* Q);
  
};
}
}
}
