/*
 * translator.cpp
 *
 *  Created on: Jan 20, 2015
 *      Author: dejan
 */

#include "engine/translator/translator.h"

#include "smt/factory.h"

#include <sstream>
#include <iostream>

namespace sal2 {
namespace output {

translator::translator(const system::context& ctx)
: engine(ctx)
{
}

translator::~translator() {
}

engine::result translator::query(const system::transition_system* ts, const system::state_formula* sf) {
  return UNKNOWN;
}

const system::state_trace* translator::get_trace() {
  throw exception("Not supported.");
}

}
}
