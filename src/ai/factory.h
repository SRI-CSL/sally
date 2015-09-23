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

#include "ai/analyzer.h"

namespace boost { namespace program_options {
  class options_description;
}}

namespace sally {

/**
 * Factory to create abstract interpretation analyers.
 */
class analyzer_factory {

public:

  /** Construct an engine of the given name */
  static
  analyzer* mk_analyzer(std::string id, const system::context& ctx);

  /** Get all the analyzers to setup the options */
  static
  void setup_options(boost::program_options::options_description& options);

  /** Get the list of all analyzers */
  static
  void get_analyzers(std::vector<std::string>& out);

};

}
