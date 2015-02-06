/*
* options.cpp
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#include "utils/options.h"

#include <boost/program_options/variables_map.hpp>

namespace sally {

options::options(const boost::program_options::variables_map& options)
: d_options(&options)
, d_my_options(0)
{}

options::options()
{
  d_my_options = new boost::program_options::variables_map();
  d_options = d_my_options;
}

options::~options() {
  delete d_my_options;
}

bool options::has_option(std::string opt) const {
  return d_options->count(opt) > 0;
}

std::string options::get_string(std::string opt) const {
  return d_options->at(opt).as<std::string>();
}

unsigned options::get_unsigned(std::string opt) const {
  return d_options->at(opt).as<unsigned>();
}

int options::get_int(std::string opt) const {
  return d_options->at(opt).as<int>();
}

bool options::get_bool(std::string opt) const {
  return d_options->count(opt) > 0;
}

}

