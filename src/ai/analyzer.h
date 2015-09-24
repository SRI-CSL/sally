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
#include "expr/model.h"
#include "expr/gc_participant.h"
#include "system/context.h"
#include "system/state_trace.h"

#include <string>

namespace sally {

/**
 * Abstract abstract analyzer, an entry point for creating new analyzers.
 */
class analyzer : public expr::gc_participant {

  /** The context */
  const system::context& d_ctx;

protected:

  /** Returns the context of the analyzer */
  const system::context& ctx() const;

  /** Returns the term manager of the analyzer */
  expr::term_manager& tm() const;

public:

  /** Create the analyzer for the transition system */
  analyzer(const system::context& ctx);

  /** Destructor */
  virtual
  ~analyzer();

  /** Start the analyzer with the transition system and the property of interest */
  virtual
  void start(const system::transition_system* ts, const system::state_formula* p) = 0;

  /** Reset error */
  virtual
  void clear() = 0;

  /** Notification of new reachable states at frame k */
  virtual
  void notify_reachable(system::state_trace* trace) = 0;

  /** Notification of unreachable states at frame k */
  virtual
  void notify_unreachable(size_t k, const expr::model::ref m) = 0;

  /** Output new inferences (potential invariants) */
  virtual
  void infer(std::vector<expr::term_ref>& output) = 0;

};

}
