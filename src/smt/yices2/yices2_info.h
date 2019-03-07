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

#ifdef WITH_YICES2

#include "smt/yices2/yices2.h"

#include <boost/program_options.hpp>

namespace sally {
namespace smt {

struct yices2_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("yices2-mode", value<std::string>()->default_value("hybrid"), "Mode of Yices2 to use (dpllt, mcsat, hybrid).")
        ("yices2-trace-tags", value<std::string>(), "Comma separated to pass to (debug version of) Yices2.")
        ;
  }

  static std::string get_id() {
    return "yices2";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new yices2(ctx.tm, ctx.opts, ctx.stats);
  }

};

}
}

#endif
