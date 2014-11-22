/*
 * exception.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include <string>
#include <iosfwd>

namespace sal2 {

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
