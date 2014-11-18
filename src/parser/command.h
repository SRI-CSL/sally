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
    DECLARE_STATE_TYPE,
    DEFINE_STATES
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


/**
 * Command to declare a state type.
 */
class declare_state_type_command : public command {

  /** The state type */
  expr::state_type d_state_type;

public:

  declare_state_type_command(std::string id, expr::term_ref state_type)
  : command(DECLARE_STATE_TYPE)
  , d_state_type(id, state_type)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_type_string() << ": " << d_state_type << "]";
  }
};

class define_states_command : public command {

  /** The state formula defining the set of states */
  expr::state_formula d_state_formula;

public:

  define_states_command(const expr::state_formula& state_formula)
  : command(DEFINE_STATES)
  , d_state_formula(state_formula)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_type_string() << ": " << d_state_formula << "]";
  }

};

}
}
