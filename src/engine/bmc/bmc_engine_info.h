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

#include "engine/bmc/bmc_engine.h"

#include <boost/program_options/options_description.hpp>

namespace sally {
namespace bmc {

struct bmc_engine_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("bmc-max", value<unsigned>()->default_value(10), "Maximal unrolling length to check.")
        ("bmc-min", value<unsigned>()->default_value(0), "Minimal unrolling length to check.")
        ;
  }

  static std::string get_id() {
    return "bmc";
  }

  static engine* new_instance(const system::context& ctx) {
    return new bmc_engine(ctx);
  }

};

}
}
