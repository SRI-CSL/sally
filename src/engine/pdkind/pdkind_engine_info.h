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

#include "engine/pdkind/pdkind_engine.h"

#include <boost/program_options.hpp>

#include <string>

namespace sally {
namespace pdkind {

struct pdkind_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("pdkind-max", value<unsigned>()->default_value(0), "Maximal frame to consider.")
        ("pdkind-add-backward", "Add learnts to previous frames in reachability checks.")
        ("pdkind-check-deadlock", "Check for deadlocks throughout the algorithm.")
        ("pdkind-induction-max", value<unsigned>()->default_value(0), "Max induction depth")
        ("pdkind-minimize-interpolants", "Try to minimize interpolants")
        ("pdkind-minimize-generalizations", "Try to minimize generalizations")
        ("pdkind-minimize-frames", "Try to minimize frames")
        ("pdkind-output-cex-graph", value<std::string>(), "Print the CEX graph into this file when done.")
        ;
  }

  static std::string get_id() {
    return "pdkind";
  }

  static engine* new_instance(const system::context& ctx) {
    return new pdkind_engine(ctx);
  }

};

}
}
