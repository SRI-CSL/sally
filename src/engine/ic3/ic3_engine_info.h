/*
 * ic3_engine_info.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "engine/ic3/ic3_engine.h"

#include <boost/program_options.hpp>

namespace sally {
namespace ic3 {

struct ic3_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    options.add_options()
        ("ic3-use-weakening", "Use weakening in forward reasoning.")
        ("ic3-show-invariant", "Show the invariant if a property is proved true.")
        ("ic3-pdr", "Focus only on the property.")
        ("ic3-aggresive-reduce", "Do aggressive learnts reduction")
        ;
  }

  static std::string get_id() {
    return "ic3";
  }

  static engine* new_instance(const system::context& ctx) {
    return new ic3_engine(ctx);
  }

};

}
}
