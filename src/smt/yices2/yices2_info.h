/*
 * yices2_info.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
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
  }

  static std::string get_id() {
    return "yices2";
  }

  static solver* new_instance(const solver_context& ctx) {
    return new yices2(ctx.tm, ctx.opts);
  }

};

}
}

#endif
