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
, d_ts(0)
, d_property(0)
{
}

interval_analyzer::~interval_analyzer() {
}

void interval_analyzer::start(const system::transition_system* ts, const system::state_formula* p) {
  TRACE("interval") << "interval_analyzer::start()" << std::endl;
  d_ts = ts;
  d_property = p;
  clear();
}

void interval_analyzer::clear() {
  TRACE("interval") << "interval_analyzer::clear()" << std::endl;
  d_variable_value_info.clear();
  d_potential_invariants.clear();
}

void interval_analyzer::notify_reachable(system::trace_helper* trace) {
  TRACE("interval") << "interval_analyzer::notify_reachable(): " << std::endl;
  TRACE("interval") << *trace << std::endl;

  // The state variables
  const std::vector<expr::term_ref>& state_variables = d_ts->get_state_type()->get_variables(system::state_type::STATE_CURRENT);

  // The term manager
  expr::term_manager& tm = ctx().tm();

  // The model
  expr::model::ref m = trace->get_model();

  // Go through the frames
  for (size_t k = 0; k < trace->size(); ++ k) {
    // Update variables for k-th frame
    for (size_t i = 0; i < state_variables.size(); ++ i) {
      expr::term_ref x = state_variables[i];
      if (tm.type_of(x) == tm.real_type()) {
        expr::term_ref x_k = trace->get_state_formula(x, k);
        expr::value x_value = m->get_variable_value(x_k);
        assert(!x_value.is_null());
        value_info& x_info = d_variable_value_info[x];

        // Update min
        if (x_info.min_reachable.is_null() || x_value.get_rational() < x_info.min_reachable.get_rational()) {
          x_info.min_reachable = x_value;
          // Did we invalidate the max unreachable
          if (!x_info.max_unreachable_below.is_null() && x_info.max_unreachable_below.get_rational() >= x_value.get_rational()) {
            x_info.max_unreachable_below = expr::value();
          }
        }

        // Update max
        if (x_info.max_reachable.is_null() || x_value.get_rational() > x_info.max_reachable.get_rational()) {
          x_info.max_reachable = x_value;
          // Did we invalidate the min unreachable
          if (!x_info.min_unreachable_above.is_null() && x_info.min_unreachable_above.get_rational() <= x_value.get_rational()) {
            x_info.min_unreachable_above = expr::value();
          }
        }

      }
    }
  }

  TRACE("interval::internal") << *this << std::endl;
}


void interval_analyzer::notify_unreachable(size_t k, const expr::model::ref m) {
  TRACE("interval") << "interval_analyzer::notify_unreachable(" << k << "): " << std::endl;
  TRACE("interval") << *m << std::endl;

  // The term manager
  expr::term_manager& tm = ctx().tm();

  // The state variables
  const std::vector<expr::term_ref>& state_variables = d_ts->get_state_type()->get_variables(system::state_type::STATE_CURRENT);

  for (size_t i = 0; i < state_variables.size(); ++ i) {
    expr::term_ref x = state_variables[i];
    if (tm.type_of(x) == tm.real_type()) {
      expr::value x_value = m->get_variable_value(x);
      assert(!x_value.is_null());
      value_info& x_info = d_variable_value_info[x];

      // If we have min reachable, see if we can update max unreachable
      if (!x_info.min_reachable.is_null()) {
        if (x_value.get_rational() < x_info.min_reachable.get_rational()) {
          if (x_info.max_unreachable_below.is_null() || x_value.get_rational() > x_info.max_unreachable_below.get_rational()) {
            x_info.max_unreachable_below = x_value;

            // Construct the potential invariant x > value
            expr::rational bound = expr::rational::value_between(x_info.max_unreachable_below.get_rational(), x_info.min_reachable.get_rational());
            expr::term_ref value_term = tm.mk_rational_constant(bound);
            expr::term_ref ineq = tm.mk_term(expr::TERM_GT, x, value_term);
            d_potential_invariants.push_back(ineq);
          }
        }
      }

      // If we have max reachable, see if we can update min unreachable
      if (!x_info.max_reachable.is_null()) {
        if (x_value.get_rational() > x_info.max_reachable.get_rational()) {
          if (x_info.min_unreachable_above.is_null() || x_value.get_rational() < x_info.min_unreachable_above.get_rational()) {
            x_info.min_unreachable_above = x_value;

            // Construct the potential invariant x < value
            expr::rational bound = expr::rational::value_between(x_info.max_reachable.get_rational(), x_info.min_unreachable_above.get_rational());
            expr::term_ref value_term = tm.mk_rational_constant(bound);
            expr::term_ref ineq = tm.mk_term(expr::TERM_LT, x, value_term);
            d_potential_invariants.push_back(ineq);
          }
        }
      }
    }
  }

  TRACE("interval::internal") << *this << std::endl;
}

void interval_analyzer::gc_collect(const expr::gc_relocator& gc_reloc) {
}

void interval_analyzer::to_stream(std::ostream& out) const {
  variable_value_info::const_iterator it = d_variable_value_info.begin();
  for (; it != d_variable_value_info.end(); ++ it) {
    out << it->first << ": [";
    out << it->second.max_unreachable_below << " < " << it->second.min_reachable << " <= " << it->second.max_reachable << " < " << it->second.min_unreachable_above;
    out << "]" << std::endl;
  }
}

std::ostream& operator << (std::ostream& out, const interval_analyzer& ia) {
  ia.to_stream(out);
  return out;
}

void interval_analyzer::infer(std::vector<expr::term_ref>& output) {
  TRACE("interval") << "interval_analyzer::infer(): " << std::endl;
  TRACE("interval::internal") << *this << std::endl;

  assert(output.empty());
  output.swap(d_potential_invariants);
}

}
}
