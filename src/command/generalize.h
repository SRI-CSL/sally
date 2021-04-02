#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"
#include "expr/model.h"

#include <vector>
#include <set>

namespace sally {
namespace cmd {

/** Command to generalize two state formulas. */
class generalize : public command {

  system::state_formula* d_F;
  expr::model::ref d_m;
  std::set<expr::term_ref> d_vars_to_eliminate;
  std::set<expr::term_ref> d_vars_to_keep;

public:

  /** generalize takes over the state formula */
  generalize(system::state_formula* F,
      const std::vector<expr::term_ref>& variables,
      const std::vector<expr::term_ref>& values,
      const std::vector<expr::term_ref>& vars_to_eliminate);

  /** Command owns, so we delete it */
  ~generalize();

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
