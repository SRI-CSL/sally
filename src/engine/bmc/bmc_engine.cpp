/*
 * bmc_engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/bmc/bmc_engine.h"

namespace sal2 {
namespace bmc {

engine* bmc_engine_info::new_instance() {
  return new bmc_engine();
}

void bmc_engine_info::add_options(boost::program_options::options_description& options) {
  using namespace boost::program_options;
  options.add_options()
      ("bmc_max", value<unsigned>()->default_value(100), "Maximal unrolling length.")
      ;
}

bmc_engine::bmc_engine() {
}

bmc_engine::~bmc_engine() {
}


bmc_engine::result bmc_engine::query(const system::transition_system& ts, const system::state_formula* sf) {
  return UNSUPPORTED;
}

}
}
