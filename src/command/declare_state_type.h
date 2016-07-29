#pragma once

#include "command.h"

#include "system/state_type.h"

namespace sally {
namespace cmd {

/** Command to declared a state type. */
class declare_state_type_command : public command {

  /** Id if any */
  std::string d_id;

  /** The type */
  system::state_type* d_state_type;

public:

  /** Create a command to declare a state type. */
  declare_state_type_command(std::string state_id, system::state_type* state_type);

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

}
}
