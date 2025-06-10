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

#include <string>
#include <iosfwd>
#include <ctime>
#include <boost/program_options.hpp>

namespace sally {
namespace utils {

class stat {
  std::string d_name;
  std::string d_format_id;
  std::string d_description;
public:
  stat(std::string name, std::string format_id, std::string description) : d_name(name), d_format_id(format_id), d_description(description) {}
  virtual ~stat() {}
  std::string get_name() const { return d_name; }
  std::string get_format_id() const { return d_format_id; }
  std::string get_description() const { return d_description; }
  virtual void to_stream(std::ostream& out) const = 0;
  virtual std::string to_string() const = 0;
};

std::ostream& operator << (std::ostream& out, const stat& s);

/** String valued statistic */
class stat_string : public stat {
  std::string d_value;
public:
  stat_string(std::string name, std::string format_id, std::string description)
  : stat(name, format_id, description)
  { d_value = ""; }
  std::string& get_value() { return d_value; }
  void set_value(std::string value) { d_value = value; }
  void to_stream(std::ostream& out) const { out << d_value; }
  std::string to_string() const { return d_value; }
};

/** Double valued statistic */
class stat_double : public stat {
  double d_value;
public:
  stat_double(std::string name, std::string format_id, std::string description)
  : stat(name, format_id, description) 
  { d_value = 0; }
  double& get_value() { return d_value; }
  void set_value(double value) { d_value = value; }
  void to_stream(std::ostream& out) const;
  std::string to_string() const { return std::to_string(d_value); }
};

/** Integer valued statistic */
class stat_int : public stat {
  int d_value;
public:
  stat_int(std::string name, std::string format_id, std::string description)
  : stat(name, format_id, description) 
  { d_value = 0; }
  int& get_value() { return d_value; }
  void set_value(int value) { d_value = value; }
  void to_stream(std::ostream& out) const;
  std::string to_string() const { return std::to_string(d_value); }
};

/** Timer statistic */
class stat_timer : public stat {
  double d_elapsed;
  bool d_started;
  std::clock_t d_start_time;
public:
  stat_timer(std::string name, std::string format_id, std::string description);
  void start();
  void stop();
  double get_elapsed() const { return d_elapsed; }
  void to_stream(std::ostream& out) const;  
  std::string to_string() const;
};

/** Collection of statistics */
class statistics {

  /** Statistics by name */
  std::map<std::string, stat*> d_stats;

  /** If locked, we can not add more statistics */
  bool d_locked;

  /** Add a statistic to d_stats. If a statistic with the same name already exists, no action is taken. */
  void add_string(std::string name, std::string format_id, std::string description);
  void add_double(std::string name, std::string format_id, std::string description);
  void add_int(std::string name, std::string format_id, std::string description);
  void add_timer(std::string name, std::string format_id, std::string description);

public:

  statistics();
  ~statistics();

  /** Get format help string */
  std::string get_help_string() const;

  /** Take over the pointer to the statistic. If the statistic does not exist, one is created. */
  stat* register_stat(std::string name);

  /** Lock, i.e. no more additional statistics */
  void lock();

  /** Output headers to stream */
  void headers_to_stream(std::ostream& out) const;

  /** Output current values to stream */
  void values_to_stream(std::ostream& out) const;

  /** Print to headers and values to the stream */
  void to_stream(std::string prefix, std::ostream& out) const;

  /** Print to headers and values to the stream */
  void to_stream_format(std::ostream& out) const;

  /** Return formatted string of all statistics */
  std::string format(std::string& str) const;

};

std::ostream& operator << (std::ostream& out, const statistics& stats);

}
}

