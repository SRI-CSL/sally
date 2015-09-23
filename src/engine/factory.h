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

#include "engine/engine.h"

namespace boost { namespace program_options {
  class options_description;
}}

namespace sally {

/**
 * Factory to create engines.
 */
class engine_factory {

public:

  /** Construct an engine of the given name */
  static
  engine* mk_engine(std::string id, const system::context& ctx);

  /** Get all the engines to setup the options */
  static
  void setup_options(boost::program_options::options_description& options);

  /** Get the list of all engines */
  static
  void get_engines(std::vector<std::string>& out);

};

}
