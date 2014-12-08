/*
 * bmc_engine_info.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "engine/bmc/bmc_engine.h"

#include <boost/program_options/options_description.hpp>

namespace sal2 {
namespace bmc {

struct bmc_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("bmc-max", value<unsigned>()->default_value(10), "Maximal unrolling length.")
        ;
  }

  static std::string get_id() {
    return "bmc_engine";
  }

  static engine* new_instance(const system::context& ctx) {
    return new bmc_engine(ctx);
  }

};

}
}
