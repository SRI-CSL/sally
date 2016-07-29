#pragma once

#include "command.h"

#include "system/state_formula.h"

namespace sally {
namespace cmd {

/** Command to declare a state set (formula) */
class define_states : public command {

  /** Id of the formula */
  std::string d_id;

  /** The state formula */
  system::state_formula* d_formula;

public:

  /** New command to define set of states id by given formula */
  define_states(std::string id, system::state_formula* formula);

  /** Deletes the formula if not used */
  ~define_states();

  /** Get the state formula */
  const system::state_formula* get_state_formula() const { return d_formula; }

  /** Declare the state type on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
