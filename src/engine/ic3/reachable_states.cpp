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

#include "reachable_states.h"

#include "expr/term_manager.h"

namespace sally {
namespace ic3 {

reachable_states::reachable_states(const system::state_type* state_type, utils::statistics& stats)
: d_st(state_type) {
  d_size = new utils::stat_int("sally::ic3::reachable_states::size", 0);
  stats.add(d_size);
}

reachable_states::reachable_state_id reachable_states::reachable_states::add(size_t frame, const expr::model& model, system::state_type::var_class var_class) {

  assert(var_class == system::state_type::STATE_CURRENT || var_class == system::state_type::STATE_NEXT);

  // Add to models
  reachable_state_id id = d_models.size();
  d_models.push_back(model);

  // Keep only the state variables
  expr::term_manager::substitution_map subst;
  const std::vector<expr::term_ref>& state_vars = d_st->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& model_vars = d_st->get_variables(var_class);
  assert(state_vars.size() == model_vars.size());
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    subst[model_vars[i]] = state_vars[i];
  }
  d_models.back().restrict_vars_to(subst);

  // Make sure it's big enough
  if (d_reachable.size() <= frame) {
    d_reachable.resize(frame + 1);
  }

  // Add the model
  d_reachable[frame].insert(id);

  return id;
}

}
}
