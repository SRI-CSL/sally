/*
 * factory.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#pragma once

#include "engine/engine.h"

#include <boost/program_options/options_description.hpp>

namespace sal2 {

/**
 * Factory to create engines.
 */
class factory {

public:

  /** Construct an engine of the given name */
  static
  engine* mk_engine(std::string id, const system::context& ctx);

  /** Get all the engines to setup the options */
  static
  void setup_options(boost::program_options::options_description& options);

  /** Get the list of all engines */
  static
  void get_engines(std::vector<std::string>& out);

};


}
