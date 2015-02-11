/*
 * statistics.h
 *
 *  Created on: Feb 11, 2015
 *      Author: dejan
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

