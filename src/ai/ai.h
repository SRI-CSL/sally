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

#include <string>

namespace sally {
namespace ai {

/**
 * Abstract interpreter class, and an entry point for creating new engines.
 */
class abstract_interpreter : public expr::gc_participant {

  /** The context */
  const system::context& d_ctx;

protected:

  /** Returns the context of the engine */
  const system::context& ctx() const;

  /** Returns the term manager of the engine */
  expr::term_manager& tm() const;

public:

  /** Create the engine */
  abstract_interpreter(const system::context& ctx);

  virtual
  ~abstract_interpreter() {};

  /** Run the interpreter on the engine */
  virtual
  void run(system::transition_system* ts) = 0;

};

}
}
