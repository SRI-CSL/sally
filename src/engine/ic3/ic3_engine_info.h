/*
 * ic3_engine_info.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "engine/ic3/ic3_engine.h"

#include <boost/program_options.hpp>

namespace sal2 {
namespace ic3 {

struct ic3_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("ic3-max-frames", value<unsigned>()->default_value(10), "Maximal number of frames.")
        ("ic3-max-frame-size", value<unsigned>()->default_value(50), "Maximal number of facts per frame.")
        ;
  }

  static std::string get_id() {
    return "ic3-engine";
  }

  static engine* new_instance(const system::context& ctx) {
    return new ic3_engine(ctx);
  }

};

}
}
