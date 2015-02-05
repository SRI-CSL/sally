/*
 * kind_engine_info.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "engine/kind/kind_engine.h"

#include <boost/program_options.hpp>

namespace sally {
namespace kind {

struct kind_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("kind-max", value<unsigned>()->default_value(10), "Maximal k for k-induction.")
        ("kind-min", value<unsigned>()->default_value(0), "Minimal k for k-induction.")
        ;
  }

  static std::string get_id() {
    return "kind";
  }

  static engine* new_instance(const system::context& ctx) {
    return new kind_engine(ctx);
  }

};

}
}
