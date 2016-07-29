#pragma once

#include "command.h"

#include "system/context.h"
#include "system/state_formula.h"

namespace sally {
namespace cmd {

/** Command to query a system. */
class query_command : public command {

  /** Id of the system this query is about */
  std::string d_system_id;

  /** The formula in the query querying */
  system::state_formula* d_query;

public:

  /** Query takes over the state formula */
  query_command(const system::context& ctx, std::string system_id, system::state_formula* sf);

  /** Command owns the query, so we delete it */
  ~query_command();

  /** Get the id of the system */
  std::string get_system_id() const { return d_system_id; }

  /** Get the query */
  const system::state_formula* get_query() const { return d_query; }

  /** Run the command on an engine */
  void run(system::context* ctx, engine* e);

  /** Output the command to stream */
  void to_stream(std::ostream& out) const;
};

}
}
