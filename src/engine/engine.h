/*
 * engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/transition_system.h"

#include <string>
#include <boost/program_options.hpp>

namespace sal2 {

/**
 * Abstract engine class, and an entrypoint for creating new engines.
 */
class engine  {

public:

  enum result {
    /** The property is valid */
    VALID,
    /** The property is invalid */
    INVALID,
    /** The query type is not supported by the engine */
    UNSUPPORTED,
    /** The engine was interrupted */
    INTERRUPTED
  };

  /** Construct an engine of the given name */
  static
  engine* mk_engine(std::string id);

  /** Get all the engines to setup the options */
  static
  void add_options(boost::program_options::options_description& options);

  /** Get the list of all engines */
  static
  void get_engines(std::vector<std::string>& out);

  /** Query the engine */
  virtual
  result query(const system::transition_system& ts, const system::state_formula* sf) = 0;

  virtual
  ~engine() {};
};

}
