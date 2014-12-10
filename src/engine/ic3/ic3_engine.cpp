/*
 * ic3_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/ic3/ic3_engine.h"

#include "smt/factory.h"
#include "system/state_trace.h"

#include <sstream>
#include <iostream>

namespace sal2 {
namespace ic3 {

ic3_engine::ic3_engine(const system::context& ctx)
: engine(ctx)
{
}

ic3_engine::~ic3_engine() {
}

ic3_engine::result ic3_engine::query(const system::transition_system& ts, const system::state_formula* sf) {
  return UNKNOWN;
}

const system::state_trace* ic3_engine::get_trace() {
  return 0;
}


}
}
