/*
 * exception.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include <string>

namespace sal2 {

class exception {

protected:

  std::string d_msg;

  exception() {}

public:

  exception(std::string msg)
  : d_msg(msg)
  {}

  virtual ~exception() {}

  virtual void toStream(std::ostream& out) const {
    out << d_msg;
  }
};

inline
std::ostream& operator << (std::ostream& out, const exception& e) {
  e.toStream(out);
  return out;
}


}
