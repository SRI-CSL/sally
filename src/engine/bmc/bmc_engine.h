/*
 * bmc_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "system/context.h"
#include "system/state_trace.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sal2 {
namespace bmc {

/**
 * Bounded model checking engine.
 */
class bmc_engine : public engine {

  /** SMT solver we're using */
  smt::solver* d_solver;

public:

  bmc_engine(const system::context& ctx);
  ~bmc_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

};

}
}
