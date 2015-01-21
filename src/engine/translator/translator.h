/*
 * translator.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sal2 {
namespace output {

/**
 * Translation engine.
 */
class translator : public engine {

public:

  translator(const system::context& ctx);
  ~translator();

  /** Query, initiates the translation */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

};

}
}
