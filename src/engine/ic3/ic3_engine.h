/*
 * ic3_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sal2 {
namespace ic3 {

class ic3_engine : public engine {

public:

  ic3_engine(const system::context& ctx);
  ~ic3_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

};

}
}
