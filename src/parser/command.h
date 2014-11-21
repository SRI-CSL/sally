/*
 * command.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include <iostream>

#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "system/transition_system.h"

namespace sal2 {
namespace parser {


class command {
public:

  /** Enumeration of all possible commands */
  enum type {
    DECLARE_STATE_TYPE,
    DEFINE_STATES,
    DEFINE_TRANSITION,
    DEFINE_TRANSITION_SYSTEM,
    QUERY
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
  std::string get_command_type_string() const;

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

  /** Id if any */
  std::string d_id;

  /** The state type */
  system::state_type d_state_type;

public:

  declare_state_type_command(std::string id, system::state_type& state_type)
  : command(DECLARE_STATE_TYPE)
  , d_id(id)
  , d_state_type(state_type)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_command_type_string() << "(" << d_id << "): " << d_state_type << "]";
  }
};

class define_states_command : public command {

  /** Id of the set (if any) */
  std::string d_id;

  /** The state formula defining the set of states */
  system::state_formula d_state_formula;

public:

  define_states_command(std::string id, const system::state_formula& state_formula)
  : command(DEFINE_STATES)
  , d_id(id)
  , d_state_formula(state_formula)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_command_type_string() << "(" << d_id << "): " << d_state_formula << "]";
  }

};

class define_transition_command : public command {

  /** Id of the transition (if any) */
  std::string d_id;

  /** The state formula defining the set of states */
  system::transition_formula d_transition_formula;

public:

  define_transition_command(std::string id, const system::transition_formula& transition_formula)
  : command(DEFINE_TRANSITION)
  , d_id(id)
  , d_transition_formula(transition_formula)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_command_type_string() << "(" << d_id << "): " << d_transition_formula << "]";
  }

};

class define_transition_system_command : public command {

  /** Id of the system */
  std::string d_id;

  /** The state formula defining the set of states */
  system::transition_system d_T;

public:

  define_transition_system_command(std::string id, const system::transition_system& T)
  : command(DEFINE_TRANSITION_SYSTEM)
  , d_id(id)
  , d_T(T)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_command_type_string() << "(" << d_id << "): " << d_T << "]";
  }
};

class query_command : public command {

  /** The state formula defining the set of states */
  std::string d_T;

  /** The formula we're querying */
  system::state_formula d_query;

public:

  query_command(std::string T, const system::state_formula& query)
  : command(QUERY)
  , d_T(T)
  , d_query(query)
  {}

  void to_stream(std::ostream& out) const {
    out << "[" << get_command_type_string() << " " << d_T << " : " << d_query << "]";
  }
};

}
}
