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

#include "ai/ai.h"

namespace boost { namespace program_options {
  class options_description;
}}

namespace sally {
namespace ai {

/**
 * Factory to create engines.
 */
class factory {

public:

  /** Construct an interpreter of the given name */
  static
  abstract_interpreter* mk_interpreter(std::string id, const system::context& ctx);

  /** Get all the interpreters to setup the options */
  static
  void setup_options(boost::program_options::options_description& options);

  /** Get the list of all interpreters */
  static
  void get_interpreters(std::vector<std::string>& out);

};

}
}
