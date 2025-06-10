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

#include <iostream>
#include <sstream>

namespace sally {
namespace utils {

void stat_double::to_stream(std::ostream& out) const {
  out << d_value;
}

void stat_int::to_stream(std::ostream& out) const {
  out << d_value;
}


stat_timer::stat_timer(std::string id, std::string format_id, std::string description)
: stat(id, format_id, description)
, d_elapsed(0)
, d_started(false)
, d_start_time(std::clock())
{
}

void stat_timer::start() {
  if (!d_started) {
    d_start_time = std::clock();
    d_started = true;
  }
}

void stat_timer::stop() {
  if (d_started) {
    d_elapsed += (std::clock() - d_start_time) / (double) CLOCKS_PER_SEC;
    d_started = false;
  }
}

void stat_timer::to_stream(std::ostream& out) const {
  double total = d_elapsed;
  if (d_started) {
    total += (std::clock() - d_start_time) / (double) CLOCKS_PER_SEC;
  }
  out << total;
}

std::string stat_timer::to_string() const {
  double total = d_elapsed;
  if (d_started) {
    total += (std::clock() - d_start_time) / (double) CLOCKS_PER_SEC;
  }
  return std::to_string(total);
}

statistics::statistics()
: d_locked(false)
{
  add_string("filename", "f", "Name of the input file");
  add_string("engine", "e", "Engine to use");
  add_string("solver", "s", "Solver to use");
  add_string("result", "r", "Result of the last query");
  add_timer("time", "t", "Total time");

  add_int("expr::term_manager_internal::memory_size", "tmms", "Memory size of term table");
  add_int("expr::term_manager_internal::bool_vars", "tmbv", "Number of boolean variables");
  add_int("expr::term_manager_internal::real_vars", "tmrv", "Number of real variables");
  add_int("expr::term_manager_internal::int_vars", "tmiv", "Number of integer variables");

  add_int("pdkind::frame_index", "pdkfi", "Current frame index");
  add_int("pdkind::induction_depth", "pdkid", "Current induction depth");
  add_int("pdkind::frame_size", "pdkfs", "Size of current frame");
  add_int("pdkind::frame_pushed", "pdkfp", "Number of formulas pushed to current frame");
  add_int("pdkind::queue_size", "pdkqs", "Size of obligation queue");
  add_int("pdkind::max_cex_depth", "pdkmcd", "Maximum depth of counter-example found");

  add_int("pdkind::reachable", "pdkrr", "Number of reachability queries that were proven reachable");
  add_int("pdkind::unreachable", "pdkru", "Number of reachability queries that were proven unreachable");
  add_int("pdkind::queries", "pdkrq", "Number of reachability queries");
}

statistics::~statistics() {
  for (auto& stat : d_stats) {
    delete stat.second;
  }
}

std::string statistics::get_help_string() const {
  std::stringstream help;
  help << "Statistics:\n";
  help << "  To show statistics after every command, use the --stats option.\n";
  help << "  To show live statistics, use the --live-stats option.\n";
  help << "  To show statistics in a custom format after every query, use the --stats-format option. This \n";
  help << "    option takes a string and replaces all occurrences of %<format_id> with the value of the \n";
  help << "    statistic. For example, to show the input filename and the result of the last query with a \n";
  help << "    space between them, use --stats-format \"%f %r\".\n\n";

  // Compute the maximum length of the name and format
  size_t max_name_length = 0;
  size_t max_format_length = 9;
  for (auto& stat : d_stats) {
    max_name_length = std::max(max_name_length, stat.second->get_name().length());
    max_format_length = std::max(max_format_length, stat.second->get_format_id().length());
  }

  // Print out the statistics, left-aligned
  help << "Available statistics:\n";
  help << "  Name";
  help << std::string(max_name_length - 4, ' ');
  help << "  Format ID";
  help << std::string(max_format_length - 9, ' ');
  help << "  Description\n";
  for (auto& stat : d_stats) {
    help << "  " << stat.second->get_name();
    help << std::string(max_name_length - stat.second->get_name().length(), ' ');
    help << "  " << stat.second->get_format_id(); 
    help << std::string(max_format_length - stat.second->get_format_id().length(), ' '); 
    help << "  " << stat.second->get_description();
    help << "\n";
  }
  return help.str();
}

void statistics::add_string(std::string name, std::string format_id, std::string description) {
  if (d_stats.find(name) == d_stats.end()) {
    d_stats[name] = new stat_string(name, format_id, description);
  }
}

void statistics::add_double(std::string name, std::string format_id, std::string description) {
  if (d_stats.find(name) == d_stats.end()) {
    d_stats[name] = new stat_double(name, format_id, description);
  }
}

void statistics::add_int(std::string name, std::string format_id, std::string description) {
  if (d_stats.find(name) == d_stats.end()) {
    d_stats[name] = new stat_int(name, format_id, description);
  }
}

void statistics::add_timer(std::string name, std::string format_id, std::string description) {
  if (d_stats.find(name) == d_stats.end()) {
    d_stats[name] = new stat_timer(name, format_id, description);
  }
}

stat* statistics::register_stat(std::string name) {
  if (d_stats.find(name) == d_stats.end()) {
    add_timer(name, "", "");
  }
  return d_stats[name];
}

void statistics::lock() {
  d_locked = true;
}

void statistics::headers_to_stream(std::ostream& out) const {
  bool first = true;
  for (auto& stat : d_stats) {
    if (!first) {
      out << "\t";
    }
    out << stat.second->get_name();
    first = false;
  }
}

void statistics::values_to_stream(std::ostream& out) const {
  bool first = true;
  for (auto& stat : d_stats) {
    if (!first) {
      out << "\t";
    }
    out << stat.second->get_name();
    first = false;
  }
}

void statistics::to_stream(std::string prefix, std::ostream& out) const {
  for (auto& stat : d_stats) {
    out << prefix << stat.second->get_name() << "\t" << *stat.second << std::endl;
  }
}

std::string statistics::format(std::string& str) const {
  // Replace all the %<format_id> with the stat name
  // If the format_id is not found, leave it as is
  std::string format = str;
  for (auto& stat : d_stats) {
    size_t pos = format.find("%" + stat.second->get_format_id());
    if (pos != std::string::npos) {
      format.replace(pos, stat.second->get_format_id().length() + 1, stat.second->to_string());
    }
  }
  return format;
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

