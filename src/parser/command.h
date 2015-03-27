/*
 * command.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include <iosfwd>

#include "system/context.h"
#include "engine/engine.h"

namespace sally {
namespace parser {

class command {
public:

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

/** Command to declared a state type. */
class declare_state_type_command : public command {

  /** Id if any */
  std::string d_id;

  /** The type */
  system::state_type* d_state_type;

public:

  /** Create a command to declare a state type. */
  declare_state_type_command(std::string state_id, system::state_type* state_type)
  : command(DECLARE_STATE_TYPE)
  , d_id(state_id)
  , d_state_type(state_type)
  {}

  /** Deletes the state type if not used */
  ~declare_state_type_command();

  /** Get the id of the state type */
  std::string get_id() const { return d_id; }

  /** Get the state type itself */
  const system::state_type* get_state_type() const { return d_state_type; }

  /** Declare the state type on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;

};

/** Command to declare a state set (formula) */
class define_states_command : public command {

  /** Id of the formula */
  std::string d_id;

  /** The state formula */
  system::state_formula* d_formula;

public:

  /** New command to define set of states id by given formula */
  define_states_command(std::string id, system::state_formula* formula)
  : command(DEFINE_STATES)
  , d_id(id)
  , d_formula(formula)
  {}

  /** Deletes the formula if not used */
  ~define_states_command();

  /** Get the state formula */
  const system::state_formula* get_state_formula() const { return d_formula; }

  /** Declare the state type on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

/** Command to defined a transition (formula) */
class define_transition_command : public command {

  /** Id of the transition */
  std::string d_id;

  /** The state transition formula */
  system::transition_formula* d_formula;

public:

  /** Command to define a transition with given id */
  define_transition_command(std::string id, system::transition_formula* formula);

  /** Deletes the transition if not used */
  ~define_transition_command();

  /** Get the id of the transition */
  std::string get_id() const { return d_id; }

  /** Get the formula */
  const system::transition_formula* get_formula() const { return d_formula; }

  /** Define the transition on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

/** Command to defined a transition system */
class define_transition_system_command : public command {

  /** Id of the system */
  std::string d_id;

  /** The system */
  system::transition_system* d_system;

public:

  /** Command to define a new system with given id */
  define_transition_system_command(std::string id, system::transition_system* system)
  : command(DEFINE_TRANSITION_SYSTEM)
  , d_id(id)
  , d_system(system)
  {}

  /** Deletes the transitino system if not used */
  ~define_transition_system_command();

  /** Get the id of the system */
  std::string get_id() const { return d_id; }

  /** Get the system */
  const system::transition_system* get_system() const { return d_system; }

  /** Define the transition on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

/** Command to query a system. */
class query_command : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The formula in the query querying */
  system::state_formula* d_query;

public:

  /** Query takes over the state formula */
  query_command(const system::context& ctx, std::string system_id, system::state_formula* query)
  : command(QUERY)
  , d_system_id(system_id)
  , d_query(query)
  {}


  /** Command owns the query, so we delete it */
  ~query_command();

  /** Get the id of the system */
  std::string get_system_id() const { return d_system_id; }

  /** Get the query */
  const system::state_formula* get_query() const { return d_query; }

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

/** Command to add an assumption to the system. */
class assume_command : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The formula in the query querying */
  system::state_formula* d_assumption;

public:

  /** Query takes over the state formula */
  assume_command(const system::context& ctx, std::string system_id, system::state_formula* assumption)
  : command(ASSUME)
  , d_system_id(system_id)
  , d_assumption(assumption)
  {}


  /** Command owns the query, so we delete it */
  ~assume_command();

  /** Get the id of the system */
  std::string get_system_id() const { return d_system_id; }

  /** Get the query */
  const system::state_formula* get_assumption() const { return d_assumption; }

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};


/** A sequence of commands. */
class sequence_command : public command {

  std::vector<command*> d_commands;

public:

  /** Query takes over the state formula */
  sequence_command()
  : command(SEQUENCE)
  {}


  /** Command owns the query, so we delete it */
  ~sequence_command();

  /** Add a command to the end of the sequence */
  void push_back(command* command);

  /** Get the number of direct sub-commands */
  size_t size() const;

  /** Get the i-th command */
  command* operator [] (size_t i) const;

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};


}
}
