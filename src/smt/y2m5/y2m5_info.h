/*
 * y2m5_info.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2
#ifdef WITH_MATHSAT5

#include "smt/y2m5/y2m5.h"

#include <boost/program_options.hpp>

namespace sally {
namespace smt {

struct y2m5_info {

  static void setup_options(boost::program_options::options_description& options) {
    using namespace boost::program_options;
  }

  static std::string get_id() {
    return "y2m5";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new y2m5(ctx.tm, ctx.opts);
  }

};

}
}

#endif
#endif
