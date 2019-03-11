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
#include "expr/term_map.h"
#include "command/command.h"

#include <unordered_map>

namespace sally {
namespace parser {

struct substituition {
  expr::term_manager::substitution_map mapping;

  void add(expr::term_ref original, expr::term_ref substituted) {
    mapping.insert(std::make_pair(original, substituted));
  }

  void clear() { mapping.clear(); }
};

class chc_system {

  const system::context& ctx;

  typedef std::vector<expr::term_ref> term_vec;
  typedef expr::term_ref_hash_map<term_vec> predicate_to_rules_map;
  typedef expr::term_ref_hash_map<term_vec> prediate_to_normalized_args_map;

  /** Map from predicates to all the rules */
  predicate_to_rules_map d_rules;

  prediate_to_normalized_args_map d_normalized;

public:

  chc_system(const system::context& ctx)
  : ctx(ctx) {}

  /** Add a CHC rule */
  void add_rule(expr::term_ref head, expr::term_ref tail);

  /** Returns the command corresponding to the CHC system */
  cmd::command* to_commands();

private:

  bool is_transition_system() const;

  size_t get_number_of_predicates() const;

  substituition normalize_head(expr::term_ref &head);

  void normalize_tail(expr::term_ref &tail, const substituition &sub);

  expr::term_ref get_predicate(expr::term_ref head) const;

  term_vec get_arguments(expr::term_ref head) const;

  term_vec remove_predicate_and_extract_vars(expr::term_ref& tail, expr::term_ref predicate) const;

  cmd::command* to_transition_system() const;


};

}
}

