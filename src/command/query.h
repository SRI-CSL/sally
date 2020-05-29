#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"

#include <vector>

namespace sally {
namespace cmd {

/** Command to query a system. */
class query : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The formulas to query */
  std::vector<system::state_formula*> d_queries;

public:

  /** Query takes over the state formula */
  query(const system::context& ctx, std::string system_id, system::state_formula* q);

  /** Query takes over the state formulas */
  query(const system::context& ctx, std::string system_id, const std::vector<system::state_formula*>& queries);

  /** Command owns the query, so we delete it */
  ~query();

  /** Get the id of the system */
  std::string get_system_id() const { return d_system_id; }

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
