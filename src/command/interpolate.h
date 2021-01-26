#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"

#include <vector>

namespace sally {
namespace cmd {

/** Command to interpolate two state formulas. */
class interpolate : public command {

  system::state_formula* d_A;
  system::state_formula* d_B;

public:

  /** interpolate takes over the state formula */
  interpolate(system::state_formula* A, system::state_formula* B);

  /** Command owns, so we delete it */
  ~interpolate();

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
