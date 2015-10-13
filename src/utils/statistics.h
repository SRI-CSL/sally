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

#include <vector>
#include <string>
#include <iosfwd>
#include <ctime>

namespace sally {
namespace utils {

class stat {
  std::string d_id;
public:
  stat(std::string id)
  : d_id(id) {}
  virtual ~stat() {}
  std::string get_id() const { return d_id; }
  virtual void to_stream(std::ostream& out) const = 0;
};

std::ostream& operator << (std::ostream& out, const stat& s);

/** Column delimiter */
class stat_delimiter : public stat {
public:
  stat_delimiter(const char* delim = "|")
  : stat(delim) {}
  void to_stream(std::ostream& out) const { out << get_id(); }
};

/** Double valued statistic */
class stat_double : public stat {
  double d_value;
public:
  stat_double(std::string id, double value)
  : stat(id)
  , d_value(value)
  {}
  double& get_value() { return d_value; }
  void to_stream(std::ostream& out) const;
};

/** Integer valued statistic */
class stat_int : public stat {
  int d_value;
public:
  stat_int(std::string id, int value)
  : stat(id)
  , d_value(value)
  {}
  int& get_value() { return d_value; }
  void to_stream(std::ostream& out) const;
};

/** Timer statistic */
class stat_timer : public stat {
  double d_elapsed;
  bool d_started;
  std::clock_t d_start_time;
public:
  stat_timer(std::string id, bool on);
  void start();
  void stop();
  void to_stream(std::ostream& out) const;
};

/** Collection of statistics */
class statistics {

  /** All statistics that were added */
  std::vector<stat*> d_stats;

  /** If locked, we can not add more statistics */
  bool d_locked;

public:

  statistics();
  ~statistics();

  /** Add a statistic (takes over pointer, but you can modify the value) */
  void add(stat* s) const;

  /** Lock, i.e. no more additional statistics */
  void lock();

  /** Output headers to stream */
  void headers_to_stream(std::ostream& out) const;

  /** Output current values to stream */
  void values_to_stream(std::ostream& out) const;

};

std::ostream& operator << (std::ostream& out, const statistics& stats);

}
}

