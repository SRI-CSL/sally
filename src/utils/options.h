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

// Forward declare
namespace boost { namespace program_options {
  class variables_map;
}}

namespace sally {

/**
 * Wrapper around the options for read-only access.
 */
class options {

  /** Options passed in */
  boost::program_options::variables_map* d_options;

  /** Options created internally */
  boost::program_options::variables_map* d_my_options;

public:

  options();
  options(boost::program_options::variables_map& options);

  ~options();

  /** Check whether the option is present */
  bool has_option(std::string opt) const;

  /** Get the value of the string option opt */
  std::string get_string(std::string opt) const;

  /** Get the value of the unsigned option opt */
  unsigned get_unsigned(std::string opt) const;

  /** Set the value of the unsigned option opt */
  void set_unsigned(std::string opt, unsigned value);

  /** Get the value of the int option opt */
  int get_int(std::string opt) const;

  /** Get the value of the int option opt */
  void set_int(std::string opt, int value);

  /** Get the value of the double option opt */
  double get_double(std::string opt) const;
  
  /** Get the value of the bool option opt */
  bool get_bool(std::string opt) const;

};


}
