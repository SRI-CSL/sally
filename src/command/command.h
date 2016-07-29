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

#include <iosfwd>

#include "system/context.h"
#include "engine/engine.h"

namespace sally {
namespace cmd {

/** Enumeration of all possible commands */
enum type {
  SEQUENCE,
  DECLARE_STATE_TYPE,
  DEFINE_STATES,
  DEFINE_TRANSITION,
  DEFINE_TRANSITION_SYSTEM,
  ASSUME,
  QUERY
};

class command {
public:

  /** Construct the command */
  command(type t);

  /** Virtual destructor */
  virtual ~command() {}

  /** Output to steam */
  virtual void to_stream(std::ostream& out) const = 0;

  /** Get the type */
  type get_type() const { return d_type; }

  /** Get the type as string */
  std::string get_command_type_string() const;

  /** Run the command */
  virtual void run(system::context* ctx, engine* e) {};

private:

  /** Type of command */
  type d_type;

};

std::ostream& operator << (std::ostream& out, const command& cmd);

}
}
