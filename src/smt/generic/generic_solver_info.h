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

#include "smt/generic/generic_solver.h"

#include <string>
#include <boost/program_options/options_description.hpp>

namespace sally {
namespace smt {

struct generic_solver_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("generic-solver-script", value<std::string>(), "The SMT solver script to use (takes SMT2 from stdin).")
        ("generic-solver-logic", value<std::string>(), "The SMT logic to use (e.g. QF_LRA).")
        ("generic-solver-log", value<std::string>(), "Prefix of a file where the SMT2 output will be logged. Given 'output', the files generated will be 'output.1.smt2', ...")
        ;
  }

  static std::string get_id() {
    return "generic-solver";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new generic_solver(ctx.tm, ctx.opts, ctx.stats);
  }

};

}
}
