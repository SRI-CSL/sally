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

#ifdef WITH_GENERIC_SOLVER

#include "smt/generic/generic_solver.h"
#include "smt/incremental_wrapper.h"

#include <string>
#include <boost/program_options/options_description.hpp>


namespace sally {
namespace smt {

struct generic_solver_info {

  class generic_solver_constructor : public solver_constructor {
    expr::term_manager& d_tm;
    const options& d_opts;
    utils::statistics& d_stats;
  public:
    generic_solver_constructor(expr::term_manager& tm, const options& opts, utils::statistics& stats)
    : d_tm(tm), d_opts(opts), d_stats(stats) {}
    ~generic_solver_constructor() {};
    solver* mk_solver() { return new generic_solver(d_tm, d_opts, d_stats); }
  };

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("generic-solver-script", value<std::string>(), "The SMT solver script to use (takes SMT2 from stdin).")
        ("generic-solver-logic", value<std::string>(), "The SMT logic to use (e.g. QF_LRA).")
        ("generic-solver-log", value<std::string>(), "Prefix of a file where the SMT2 output will be logged. Given 'output', the files generated will be 'output.1.smt2', ...")
        ("generic-solver-flatten", "Run the solver in non-incremental mode.")
        ;
  }

  static std::string get_id() {
    return "generic-solver";
  }

  static std::string get_description() {
    return
        "A generic SMT-LIB compliant solver that takes SMT2 input from standard input.";
  }


  static solver* new_instance(const solver_context& ctx) {
    if (ctx.opts.get_bool("generic-solver-flatten")) {
      solver_constructor* constructor = new generic_solver_constructor(ctx.tm, ctx.opts, ctx.stats);
      return new incremental_wrapper("generic-solver-nonincremental", ctx.tm, ctx.opts, ctx.stats, constructor);
    } else {
      return new generic_solver(ctx.tm, ctx.opts, ctx.stats);
    }
  }

};

}
}

#endif