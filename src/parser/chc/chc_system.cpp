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

#include "chc_system.h"

#include "expr/term_manager.h"

using namespace sally::expr;

namespace sally {
namespace parser {

void chc_system::add_rule(term_ref head, term_ref tail) {

  // All the head variables should be distinct

  // Normalize head

  // Normalize tail

  d_rules[head].push_back(tail);
}

cmd::command* chc_system::to_commands() {
  return 0;
}


}
}


