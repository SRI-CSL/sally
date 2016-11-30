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

  /** Cache of the term manager */
  term_to_term_map& d_type_cache;

  /** Set to false whenever type computation fails */
  bool d_ok;

  void error(expr::term_ref t_ref) const;
  expr::term_ref type_of(expr::term_ref t_ref) const;
  const term& term_of(expr::term_ref t_ref) const;

public:

  type_computation_visitor(expr::term_manager_internal& tm, term_to_term_map& type_cache);

  /** Get the children of the term t that are relevant for the type computation */
  void get_children(expr::term_ref t, std::vector<expr::term_ref>& children);

  /** We visit only nodes that don't have types yet and are relevant for type computation */
  visitor_match_result match(term_ref t);

  /** Visit the term, compute type (children already type-checked) */
  void visit(term_ref t_ref);
};

}
}
