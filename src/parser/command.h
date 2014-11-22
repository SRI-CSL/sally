/*
 * command.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include <iosfwd>

#include "system/context.h"

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
  command(const system::context& ctx, type t);

  /** Virtual destructor */
  virtual ~command() {}

  /** Output to steam */
  virtual void to_stream(std::ostream& out) const = 0;

  /** Get the type */
  type get_type() const { return d_type; }

  /** Get the context */
  const system::context& get_context() const    { return d_ctx; }

  /** Get the type as string */
  std::string get_command_type_string() const;

private:

  /** The context that the command operates on */
  const system::context& d_ctx;

  /** Type of command */
  type d_type;

};

inline
std::ostream& operator << (std::ostream& out, const command& cmd) {
  cmd.to_stream(out);
  return out;
}


/**
 * Command that declared a state type.
 */
class declare_state_type_command : public command {

  /** Id if any */
  std::string d_state_id;

public:

  declare_state_type_command(const system::context& ctx, std::string state_id)
  : command(ctx, DECLARE_STATE_TYPE)
  , d_state_id(state_id)
  {}

  std::string get_state_type() const {
    return d_state_id;
  }

  void to_stream(std::ostream& out) const;
};

/** Command that declared a state formula */
class define_states_command : public command {

  /** Id of the formula (if any) */
  std::string d_id;

public:

  define_states_command(const system::context& ctx, std::string id)
  : command(ctx, DEFINE_STATES)
  , d_id(id)
  {}

  std::string get_state_formula_id() const {
    return d_id;
  }

  void to_stream(std::ostream& out) const;
};

/** Command that defined a transition */
class define_transition_command : public command {

  /** Id of the type */
  std::string d_type_id;

  /** Id of the transition */
  std::string d_transition_id;

public:

  define_transition_command(const system::context& ctx, std::string transition_id, std::string type_id)
  : command(ctx, DEFINE_TRANSITION)
  , d_transition_id(transition_id)
  {}

  std::string get_transition_id() const {
    return d_transition_id;
  }

  void to_stream(std::ostream& out) const;
};

/** Command that defined a transition system */
class define_transition_system_command : public command {

  /** Id of the system */
  std::string d_system_id;

  /** Type id */
  std::string d_type_id;

  /** Initial states */
  std::string d_initial_states;

  /** The transitions */
  std::vector<std::string> d_transitions;

public:

  define_transition_system_command(const system::context& ctx, std::string system_id, std::string type_id,
      std::string init_id, const std::vector<std::string>& transitions)
  : command(ctx, DEFINE_TRANSITION_SYSTEM)
  , d_system_id(system_id)
  , d_type_id(type_id)
  , d_initial_states(init_id)
  , d_transitions(transitions)
  {}

  std::string get_system_id() const {
    return d_system_id;
  }

  void to_stream(std::ostream& out) const;
};

/** Commmand declaring a query. */
class query_command : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The formula in the query querying */
  system::state_formula* d_query;

public:

  /** Query takes over the state formula */
  query_command(const system::context& ctx, std::string system_id, system::state_formula* query)
  : command(ctx, QUERY)
  , d_system_id(system_id)
  , d_query(query)
  {}

  ~query_command() {
    delete d_query;
  }

  std::string get_system_id() const {
    return d_system_id;
  }

  const system::state_formula* get_query() const {
    return d_query;
  }

  void to_stream(std::ostream& out) const;
};

}
}
