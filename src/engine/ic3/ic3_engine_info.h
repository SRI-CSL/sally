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
        ("ic3-enable-restarts", "Restart solvers when extending to new frame and reduce learnts.")
        ("ic3-single-solver", "One solver for reachability, one for induction, one for bmc.")
        ("ic3-dump-dependencies", "Dump reasoning dependancy graph.")
        ("ic3-max", value<unsigned>()->default_value(0), "Maximal frame to consider.")
        ("ic3-add-backward", "Add learnts to previous frames in reachability checks.")
        ("ic3-dont-extend", "Don't attempt to extend induction counter-examples.")
        ("ic3-no-initial-state", "Don't use initial state as part of induction basis")
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
