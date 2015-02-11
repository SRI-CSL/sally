/*
 * mathsat5_info.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_MATHSAT5

#include "smt/mathsat5/mathsat5.h"

#include <boost/program_options.hpp>

namespace sally {
namespace smt {

struct mathsat5_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
    options.add_options()
        ("mathsat5-generate-api-log", "Generate API logs.")
        ("mathsat5-unsat-cores", "Enable generation of unsat cores")
        ;
  }

  static std::string get_id() {
    return "mathsat5";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new mathsat5(ctx.tm, ctx.opts);
  }

};

}
}

#endif
