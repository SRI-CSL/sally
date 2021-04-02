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

#include "utils/statistics.h"
#include "utils/exception.h"

#include <iostream>

namespace sally {
namespace utils {

void stat_double::to_stream(std::ostream& out) const {
  out << d_value;
}

void stat_int::to_stream(std::ostream& out) const {
  out << d_value;
}


stat_timer::stat_timer(std::string id, bool on)
: stat(id)
, d_elapsed(0)
, d_started(on)
, d_start_time(std::clock())
{
}

void stat_timer::start() {
  if (!d_started) {
    d_start_time = std::clock();
  }
}

void stat_timer::stop() {
  d_elapsed += (std::clock() - d_start_time) / (double) CLOCKS_PER_SEC;
}

void stat_timer::to_stream(std::ostream& out) const {
  double total = d_elapsed;
  if (d_started) {
    total += (std::clock() - d_start_time) / (double) CLOCKS_PER_SEC;
  }
  out << total;
}

statistics::statistics()
: d_locked(false)
{
}

statistics::~statistics() {
  for (size_t i = 0; i < d_stats.size(); ++ i)  {
    delete d_stats[i];
  }
}

void statistics::add(stat* s) const {
  if (d_locked) {
    throw exception("Statistics already locked");
  }
  const_cast<statistics*>(this)->d_stats.push_back(s);
}

void statistics::lock() {
  d_locked = true;
}

void statistics::headers_to_stream(std::ostream& out) const {
  for (size_t i = 0; i < d_stats.size(); ++ i) {
    if (i) { out << "\t"; }
    out << d_stats[i]->get_id();
  }
}

void statistics::values_to_stream(std::ostream& out) const {
  for (size_t i = 0; i < d_stats.size(); ++ i) {
    if (i) { out << "\t"; }
    out << *d_stats[i];
  }
}

void statistics::to_stream(std::string prefix, std::ostream& out) const {
  for (size_t i = 0; i < d_stats.size(); ++ i) {
    if (!d_stats[i]->is_delimiter()) {
      out << prefix << d_stats[i]->get_id() << "\t" << *d_stats[i] << std::endl;
    }
  }
}


std::ostream& operator << (std::ostream& out, const stat& s) {
  s.to_stream(out);
  return out;
}

std::ostream& operator << (std::ostream& out, const statistics& stats) {
  stats.values_to_stream(out);
  return out;
}


}
}

