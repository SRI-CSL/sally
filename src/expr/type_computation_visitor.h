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

#include <boost/unordered_map.hpp>
#include <vector>

#include "expr/term.h"
#include "expr/term_visitor.h"

namespace sally {
namespace expr {

class term_manager_internal;

class type_computation_visitor {

  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> term_to_term_map;

  /** The term manager */
  term_manager_internal& d_tm;

  /** Cache of the term manager: term/type -> type */
  term_to_term_map& d_type_cache;

  /** Cache of the term manager: non-primitive type -> type */
  term_to_term_map& d_base_type_cache;

  /** Set to false whenever type computation fails */
  bool d_ok;

  void error(term_ref t_ref, std::string message) const;
  term_ref type_of(term_ref t_ref) const;
  term_ref base_type_of(term_ref t_ref) const;
  const term& term_of(term_ref t_ref) const;
  bool compatible(term_ref t1, term_ref t2) const;

public:

  type_computation_visitor(term_manager_internal& tm, term_to_term_map& type_cache, term_to_term_map& base_type_cache);

  // Non-null terms are good
  bool is_good_term(expr::term_ref t) const {
    return !t.is_null();
  }

  /** Get the children of the term t that are relevant for the type computation */
  void get_children(term_ref t, std::vector<term_ref>& children);

  /** We visit only nodes that don't have types yet and are relevant for type computation */
  visitor_match_result match(term_ref t);

  /** Visit the term, compute type (children already type-checked) */
  void visit(term_ref t_ref);
};

}
}
