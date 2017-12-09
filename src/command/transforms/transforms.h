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
 * Transformations to simplify the syntax of the transitions system
 * and state formulas so that solvers can handle them.
**/
class preprocessor {
public:

  preprocessor(system::context* ctx);
  
  /** JN: this current API performs transformation on each pair of
      transition system and query. This the case for the query
      command. This is very inneficient with multiple queries because
      it will transform the same transition system multiple times.
      Ideally, we would like to modify the context by replacing all
      the transition systems, formulas, etc associated with each id by
      their transformed versions. However, this requires to change the
      current API of the context class.
  **/
  
  /**
     Perform several transformations on the given T and Q.  The
     transformation is functional so it produces a new T and a new Q,
     both managed by the context. Return the id associated to the new
     T and Q.
  **/
  std::string run(std::string id, const system::transition_system* T, const system::state_formula* Q);
  
private:
  
  system::context* d_ctx;
};
}
}
}
