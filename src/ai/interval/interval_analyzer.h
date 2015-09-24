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

#include "ai/analyzer.h"

namespace sally {
namespace interval {

class interval_analyzer : public analyzer {

public:

  interval_analyzer(const system::context& ctx);
  ~interval_analyzer();

  void start(const system::transition_system* ts, const system::state_formula* p);
  void clear();

  void notify_reachable(size_t k, const expr::model::ref m);
  void notify_unreachable(size_t k, const expr::model::ref m);

  void infer(std::vector<expr::term_ref>& output);

  void gc_collect(const expr::gc_relocator& gc_reloc);
};


}
}
