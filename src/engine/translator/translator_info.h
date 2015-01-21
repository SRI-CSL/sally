/*
 * translator_info.h
 *
 *  Created on: Jan 20, 2015
 *      Author: dejan
 */

#pragma once

#include "engine/translator/translator.h"

#include <boost/program_options/options_description.hpp>

namespace sal2 {
namespace output {

struct translator_info {

  static void setup_options(boost::program_options::options_description& options) {
  }

  static std::string get_id() {
    return "translator";
  }

  static engine* new_instance(const system::context& ctx) {
    return new translator(ctx);
  }

};

}
}
