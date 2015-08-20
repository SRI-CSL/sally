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

#include "expr/model.h"
#include "system/state_type.h"
#include "utils/statistics.h"

#include <vector>
#include <set>

namespace sally {
namespace ic3 {

class reachable_states {

public:

  typedef size_t reachable_state_id;

  /** Null reachable state id */
  static const reachable_state_id reachable_state_null = (size_t)(-1);

  /** Construct the set */
  reachable_states(const system::state_type* state_type, utils::statistics& stats);

  /**
   * Add the assignment to given frame. Returns the id
   */
  reachable_state_id add(size_t frame, const expr::model& model, system::state_type::var_class var_class);

private:

  /** The state type */
  const system::state_type* d_st;

  /** Number of reachable states */
  utils::stat_int* d_size;

  /** All models (in state variables) */
  std::vector<expr::model> d_models;

  /** Set of models */
  typedef std::set<reachable_state_id> set_of_model_ids;

  /** Vector of sets of models, by frame */
  typedef std::vector<set_of_model_ids> models_by_frame;

  /** Reachable state by frame */
  models_by_frame d_reachable;
};

}
}
