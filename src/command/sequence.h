#pragma once

#include "command.h"

namespace sally {
namespace cmd {

/** A sequence of commands. */
class sequence: public command {

  std::vector<command*> d_commands;

public:

  /** Query takes over the state formula */
  sequence();

  /** Command owns the query, so we delete it */
  ~sequence();

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
