#pragma once

#include "command.h"

#include "system/transition_system.h"

namespace sally {
namespace cmd {

/** Command to defined a transition system */
class define_transition_system : public command {

  /** Id of the system */
  std::string d_id;

  /** The system */
  system::transition_system* d_system;

public:

  /** Command to define a new system with given id */
  define_transition_system(std::string id, system::transition_system* system);

  /** Deletes the transitino system if not used */
  ~define_transition_system();

  /** Get the id of the system */
  std::string get_id() const { return d_id; }

  /** Get the system */
  const system::transition_system* get_system() const { return d_system; }

  /** Define the transition on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
