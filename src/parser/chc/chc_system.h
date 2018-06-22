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

#include "system/context.h"
#include "expr/term_map.h"
#include "command/command.h"

namespace sally {
namespace parser {

class chc_system {

  const system::context& ctx;

  typedef std::vector<expr::term_ref> term_vec;
  typedef expr::term_ref_hash_map<term_vec> predicate_to_rules_map;

  /** Map from predicates to all the rules */
  predicate_to_rules_map d_rules;

public:

  chc_system(const system::context& ctx)
  : ctx(ctx) {}

  /** Add a CHC rule */
  void add_rule(expr::term_ref head, expr::term_ref tail);

  /** Returns the command corresponding to the CHC system */
  cmd::command* to_commands();
};

}
}

