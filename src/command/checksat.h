#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"

#include <vector>

namespace sally {
namespace cmd {

/** Command to checksat a formula. */
class checksat : public command {

  system::state_formula* d_F;

public:

  /** Checksat takes over the state formula */
  checksat(system::state_formula* F);

  /** Command owns, so we delete it */
  ~checksat();

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
