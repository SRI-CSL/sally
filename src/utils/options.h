/*
 * options.h
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
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
  const boost::program_options::variables_map* d_options;

  /** Options created internally */
  boost::program_options::variables_map* d_my_options;

public:

  options();
  options(const boost::program_options::variables_map& options);

  ~options();

  /** Check whether the option is present */
  bool has_option(std::string opt) const;

  /** Get the value of the string option opt */
  std::string get_string(std::string opt) const;

  /** Get the value of the unsigned option opt */
  unsigned get_unsigned(std::string opt) const;

  /** Get the value of the int option opt */
  int get_int(std::string opt) const;

  /** Get the value of the bool option opt */
  bool get_bool(std::string opt) const;

};


}
