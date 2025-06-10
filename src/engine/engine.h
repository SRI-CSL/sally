/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include "expr/term_manager.h"
#include "expr/gc_participant.h"
#include "system/context.h"
#include "../system/trace_helper.h"

#include <string>

namespace sally {

/**
 * Abstract engine class, and an entry point for creating new engines.
 */
class engine : public expr::gc_participant {

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
    SILENT,
    /** SIlent with trace */
    SILENT_WITH_TRACE,
  };

  /** The result of the last query */
  result d_last_result = UNKNOWN;

  /** Get the string representation of the result */
  std::string result_to_string(result r) const;

  /** Create the engine */
  engine(const system::context& ctx);

  virtual
  ~engine() {};

  /** Query the engine */
  virtual
  result query(const system::transition_system* ts, const system::state_formula* sf) = 0;

  /** Get the counter-example trace, if previous query allows it */
  virtual
  const system::trace_helper* get_trace() = 0;

  struct invariant {
    // The state formula
    expr::term_ref F;
    // Induction depth
    size_t depth;
    invariant(expr::term_ref F, size_t depth)
    : F(F), depth(depth) {}
  };

  /** Get the invariant, if the previous query allows it, return null if not applicable */
  virtual
  invariant get_invariant() = 0;

  /** Get the result of the last query */
  std::string get_last_result_string() const { return result_to_string(d_last_result); }

};

std::ostream& operator << (std::ostream& out, engine::result result);

}
