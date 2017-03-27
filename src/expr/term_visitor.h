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

#include <vector>
#include <boost/unordered_set.hpp>

#include "utils/hash.h"
#include "utils/trace.h"

namespace sally {
namespace expr {

enum visitor_match_result {
  /** Visit the term, but don't go deeper */
  VISIT_AND_BREAK,
  /** Visit the term, and continue with the children */
  VISIT_AND_CONTINUE,
  /** Don't visit the term, and don't go deeper */
  DONT_VISIT_AND_BREAK,
  /** Don't visit the term, but continue with the children */
  DONT_VISIT_AND_CONTINUE
};

/** Generic term visitor. */
template<typename visitor, typename term_type, typename term_type_hasher = utils::hash<term_type> >
class term_visit_topological {

  struct term_visitor_dfs_entry {
    term_type t;
    bool children_added;
    visitor_match_result visit;

    term_visitor_dfs_entry(term_type t, bool children_added, visitor_match_result visit)
    : t(t), children_added(children_added), visit(visit)
    {}
  };

  /** Visitor to notify */
  visitor& d_visitor;

public:

  /** Construct the visitor */
  term_visit_topological(visitor& v);

  /** Run the visitor on the term */
  void run(term_type t);

};


template<typename visitor, typename term_type, typename term_type_hasher>
term_visit_topological<visitor, term_type, term_type_hasher>::term_visit_topological(visitor& v)
: d_visitor(v)
{
}

template<typename visitor, typename term_type, typename term_type_hasher>
void term_visit_topological<visitor, term_type, term_type_hasher>::run(term_type t) {

  typedef boost::unordered_set<term_type, term_type_hasher> visited_set;

  // The DFS stack
  std::vector<term_visitor_dfs_entry> dfs_stack;

  // Vector to keep the children
  std::vector<term_type> children;

  // Terms already visited
  visited_set v;

  // Add initial one
  assert(d_visitor.is_good_term(t));
  dfs_stack.push_back(term_visitor_dfs_entry(t, false, d_visitor.match(t)));

  while (!dfs_stack.empty()) {

    // Process current
    term_visitor_dfs_entry& current = dfs_stack.back();

    TRACE("term::visitor") << "current: " << current.t << std::endl;

    // If visited already, we just skip it
    if (v.find(current.t) != v.end()) {
      dfs_stack.pop_back();
      continue;
    }

    // If children added, then we visit this node
    if (current.children_added) {
      if (current.visit == VISIT_AND_BREAK || current.visit == VISIT_AND_CONTINUE) {
        d_visitor.visit(current.t);
      }
      // Done with this node
      v.insert(current.t);
      dfs_stack.pop_back();
      continue;
    }

    // Children not added yet, so we add them
    current.children_added = true;
    // Whether we add them, depends on the visitor request
    if (current.visit == DONT_VISIT_AND_CONTINUE || current.visit == VISIT_AND_CONTINUE) {
      // We should add them
      children.clear();
      d_visitor.get_children(current.t, children);
      for (size_t i = 0; i < children.size(); ++ i) {
        assert(d_visitor.is_good_term(children[i]));
        dfs_stack.push_back(term_visitor_dfs_entry(children[i], false, d_visitor.match(children[i])));
      }
    }
  }
}

}
}
