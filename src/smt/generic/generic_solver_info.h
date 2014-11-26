/*
 * generic_solver_info.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#pragma once

#include "smt/generic/generic_solver.h"

#include <string>
#include <boost/program_options/options_description.hpp>

namespace sal2 {
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
    return "generic_solver";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new generic_solver(ctx.tm, ctx.opts);
  }

};

}
}
