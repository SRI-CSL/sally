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

  static std::string get_description() {
    return
        "The k-induction engine tries to prove the property in the query by checking if it is k-inductive. "
        "A property is k-inductive iff it (a) holds for the first k-steps and (b) if it holds for k-steps then"
        "it holds in step k+1. The engine can both prove properties and find counter-examples.";
  }

  static engine* new_instance(const system::context& ctx) {
    return new kind_engine(ctx);
  }

};

}
}
