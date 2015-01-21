/*
 * engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"
#include "system/context.h"
#include "system/state_trace.h"

#include <string>

namespace sal2 {

/**
 * Abstract engine class, and an entrypoint for creating new engines.
 */
class engine  {

  /** The context */
  const system::context& d_ctx;

protected:

  /** Returns the context of the engine */
  const system::context& ctx() const;

  /** Returns the term manager of the engine */
  expr::term_manager& tm() const;

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
    INTERRUPTED,
    /** Silent result (e.g. for translator) */
    SILENT
  };

  /** Create the engine */
  engine(const system::context& ctx);

  virtual
  ~engine() {};

  /** Query the engine */
  virtual
  result query(const system::transition_system* ts, const system::state_formula* sf) = 0;

  /** Get the counter-example trace, if previous query allows it */
  virtual
  const system::state_trace* get_trace() = 0;
};

std::ostream& operator << (std::ostream& out, engine::result result);

}
