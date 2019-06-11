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

#include "utils/options.h"

#include <boost/program_options/variables_map.hpp>

namespace sally {

options::options(boost::program_options::variables_map& options)
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

void options::set_unsigned(std::string opt, unsigned value) {
  d_options->at(opt).as<unsigned>() = value;
}


int options::get_int(std::string opt) const {
  return d_options->at(opt).as<int>();
}

void options::set_int(std::string opt, int value) {
  d_options->at(opt).as<int>() = value;
}

bool options::get_bool(std::string opt) const {
  return d_options->count(opt) > 0;
}

double options::get_double(std::string opt) const {
  return d_options->at(opt).as<double>();
}
  
}

