/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include "engine/ic3/ic3_engine.h"

#include <boost/program_options.hpp>

namespace sally {
namespace ic3 {

struct ic3_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("ic3-show-invariant", "Show the invariant if a property is proved true.")
        ("ic3-max", value<unsigned>()->default_value(0), "Maximal frame to consider.")
        ("ic3-add-backward", "Add learnts to previous frames in reachability checks.")
        ("ic3-check-deadlock", "Check for deadlocks throughout the algorithm.")
        ("ic3-induction-max", value<unsigned>()->default_value(0), "Max induction depth")
        ("ic3-minimize-interpolants", "Try to minimize interpolants")
        ("ic3-minimize-generalizations", "Try to minimize generalizations")
        ("ic3-minimize-frames", "Try to minimize frames")
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
