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

#include "interval_analyzer.h"

#include "utils/trace.h"

#include <iostream>


namespace sally {
namespace interval {

interval_analyzer::interval_analyzer(const system::context& ctx)
: analyzer(ctx)
{
}

interval_analyzer::~interval_analyzer() {
}

void interval_analyzer::start(const system::transition_system* ts, const system::state_formula* p) {
  TRACE("interval") << "interval_analyzer::start()" << std::endl;
}

void interval_analyzer::clear() {
  TRACE("interval") << "interval_analyzer::clear()" << std::endl;
}

void interval_analyzer::notify_reachable(const system::state_trace* trace) {
  TRACE("interval") << "interval_analyzer::notify_reachable(): " << std::endl;
  TRACE("interval") << *trace << std::endl;
}

void interval_analyzer::notify_unreachable(size_t k, const expr::model::ref m) {
  TRACE("interval") << "interval_analyzer::notify_unreachable(" << k << "): " << std::endl;
  TRACE("interval") << *m << std::endl;
}

void interval_analyzer::gc_collect(const expr::gc_relocator& gc_reloc) {
}

void interval_analyzer::infer(std::vector<expr::term_ref>& output) {
  TRACE("interval") << "interval_analyzer::infer(): " << std::endl;
}

}
}
