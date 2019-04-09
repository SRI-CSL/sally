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
#include <sstream>

namespace sally {

namespace expr {
  class term_manager;
}

/**
 * Generic exception class for SAL error reporting.
 */
class exception {

protected:

  /** The message */
  std::stringstream d_msg;

  /** No empty exceptions */
  exception() {}

public:

  /** Create an exception with the given message */
  exception(std::string msg)
  : d_msg()
  {
    d_msg << msg;
  }

  /** Create an exception and set it up with the given term manager */
  exception(expr::term_manager* tm);
  exception(expr::term_manager& tm);

  exception(const exception& e);

  virtual ~exception() {}

  /** Output the exception to the stream */
  virtual void to_stream(std::ostream& out) const;

  /** Return the message */
  std::string get_message() const { return d_msg.str(); }

  /** Append to the message */
  template <typename T>
  exception& operator << (const T& t) {
    d_msg << t;
    return *this;
  }

};

std::ostream& operator << (std::ostream& out, const exception& e);


}
