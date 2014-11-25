/*
 * engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/context.h"

#include <string>
#include <boost/program_options/options_description.hpp>

namespace sal2 {

/**
 * Abstract engine class, and an entrypoint for creating new engines.
 */
class engine  {

  /** The context */
  const system::context& d_ctx;

public:

  enum result {
    /** The property is valid */
    VALID,
    /** The property is invalid */
    INVALID,
    /** The result is inconclusive */
    UNKNOWN,
    /** The query type is not supported by the engine */
    UNSUPPORTED,
    /** The engine was interrupted */
    INTERRUPTED
  };

  /** Construct an engine of the given name */
  static
  engine* mk_engine(std::string id, const system::context& ctx);

  /** Get all the engines to setup the options */
  static
  void setup_options(boost::program_options::options_description& options);

  /** Get the list of all engines */
  static
  void get_engines(std::vector<std::string>& out);

  /** Query the engine */
  virtual
  result query(const system::transition_system& ts, const system::state_formula* sf) = 0;

  /** Create the engine */
  engine(const system::context& ctx);

  virtual
  ~engine() {};

  /** Returns the context of the engine */
  const system::context& ctx() const;

  /** Returns the term manager of the engine */
  expr::term_manager& tm() const;

};

std::ostream& operator << (std::ostream& out, engine::result result);

}
