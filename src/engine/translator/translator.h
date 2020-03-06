/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

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
  const system::trace_helper* get_trace();

  /** Invariant (not supported) */
  invariant get_invariant();

  /** Nothing to do */
  void gc_collect(const expr::gc_relocator& gc_reloc) {}
};

}
}
