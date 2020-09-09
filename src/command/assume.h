#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

namespace sally {
namespace cmd {

/** Command to add an assumption to the system. */
class assume : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The state formula to assume on init and transitions */
  system::state_formula* d_assumption_state;

  /** The transition formula to assume on transitions */
  system::transition_formula* d_assumption_transition;

public:

  /** Command takes over the state formula */
  assume(const system::context& ctx, std::string system_id, system::state_formula* assumption);

  /** Command takes over the transition formula */
  assume(const system::context& ctx, std::string system_id, system::transition_formula* assumption);

  /** Command owns the query, so we delete it */
  ~assume();

  /** Get the id of the system */
  std::string get_system_id() const { return d_system_id; }

  /** Get the query */
  const system::state_formula* get_assumption() const { return d_assumption_state; }

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
