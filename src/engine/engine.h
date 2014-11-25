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
