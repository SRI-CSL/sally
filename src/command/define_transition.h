#pragma once

#include "command.h"

#include "system/transition_formula.h"

namespace sally {
namespace cmd {

/** Command to defined a transition (formula) */
class define_transition : public command {

  /** Id of the transition */
  std::string d_id;

  /** The state transition formula */
  system::transition_formula* d_formula;

public:

  /** Command to define a transition with given id */
  define_transition(std::string id, system::transition_formula* formula);

  /** Deletes the transition if not used */
  ~define_transition();

  /** Get the id of the transition */
  std::string get_id() const { return d_id; }

  /** Get the formula */
  const system::transition_formula* get_formula() const { return d_formula; }

  /** Define the transition on given context. */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
