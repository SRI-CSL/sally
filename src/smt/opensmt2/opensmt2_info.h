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

#ifdef WITH_OPENSMT2

#include "smt/opensmt2/opensmt2.h"

#include <boost/program_options.hpp>

namespace sally {
namespace smt {

struct opensmt2_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("opensmt2-itp", value<int>(), "Choose interpolation algorithm")
        ;
  }

  static std::string get_id() {
    return "opensmt2";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new opensmt2(ctx.tm, ctx.opts, ctx.stats);
  }

};

}
}

#endif // WITH_OPENSMT2

