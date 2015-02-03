/*
 * translator.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sally {
namespace output {

/**
 * Translation engine.
 */
class translator : public engine {

  const system::transition_system* d_ts;
  const system::state_formula* d_sf;

  /** Output the problem */
  void to_stream_mcmt(std::ostream& out) const;

  /** Output the problem */
  void to_stream_nuxmv(std::ostream& out) const;

  /** Output the problem */
  void to_stream_horn(std::ostream& out) const;

  /** Output the problem */
  void to_stream_lustre(std::ostream& out) const;

public:

  translator(const system::context& ctx);
  ~translator();

  /** Query, initiates the translation */
  result query(const system::transition_system* ts, const system::state_formula* sf);

  /** Trace */
  const system::state_trace* get_trace();

};

}
}
