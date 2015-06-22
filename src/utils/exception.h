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
#include <iosfwd>

namespace sally {

/**
 * Generic exception class for SAL error reporting.
 */
class exception {

protected:

  /** The message */
  std::string d_msg;

  /** No empty exceptions */
  exception() {}

public:

  /** Create an exception with the fiven message */
  exception(std::string msg)
  : d_msg(msg)
  {}

  virtual ~exception() {}

  /** Output the exception to the stream */
  virtual void to_stream(std::ostream& out) const;

  /** Return the message */
  std::string get_message() const { return d_msg; }
};

std::ostream& operator << (std::ostream& out, const exception& e);

}
