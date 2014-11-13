/*
 * command.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include <iostream>

#include "expr/state.h"

namespace sal2 {
namespace parser {


class command {
public:

  /** Enumeration of all possible commands */
  enum type {
    DECLARE_STATE_TYPE
  };

  /** Construct the command */
  command(type t);

  /** Virtual destructor */
  virtual ~command() {}

  /** Output to steam */
  virtual void to_stream(std::ostream& out) const = 0;

  /** Get the type */
  type get_type() const { return d_type; }

  /** Get the type as string */
  std::string get_type_string() const;

protected:

  /** Type of command */
  type d_type;
};

inline
std::ostream& operator << (std::ostream& out, const command& cmd) {
  cmd.to_stream(out);
  return out;
}

class declare_state_type_command : public command {

  expr::term_ref d_state_type;

public:

  declare_state_type_command(expr::term_ref state_type)
  : command(DECLARE_STATE_TYPE)
  , d_state_type(state_type)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_type_string() << ": " << d_state_type << "]";
  }
};

}
}
