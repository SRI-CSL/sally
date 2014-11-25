/*
 * factory_engines.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

//
// ADD ALL THE ENGINES HERE
//

#include "engine/bmc/bmc_engine_info.h"
#include "engine/kind/kind_engine_info.h"

sal2::engine_data::engine_data() {
  add_engine_info<bmc::bmc_engine_info>();
  add_engine_info<kind::kind_engine_info>();
}

