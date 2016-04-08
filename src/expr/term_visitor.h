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

#include "term.h"
#include "term_manager.h"

#include <vector>
#include <boost/unordered_set.hpp>

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
template<typename visitor>
class term_visit_topological {

  /** The term manager */
  const term_manager& d_tm;

  /** Visitor to notify */
  visitor& d_visitor;

public:

  /** Construct the visitor */
  term_visit_topological(const term_manager& tm, visitor& v);

  /** Run the visitor on the term */
  void run(term_ref t);

};


template<typename visitor>
term_visit_topological<visitor>::term_visit_topological(const term_manager& tm, visitor& v)
: d_tm(tm)
, d_visitor(v)
{
}

struct dfs_entry {
  term_ref t;
  bool children_added;
  visitor_match_result visit;

  dfs_entry(term_ref t, bool children_added, visitor_match_result visit)
  : t(t), children_added(children_added), visit(visit)
  {}
};

template<typename visitor>
void term_visit_topological<visitor>::run(term_ref t) {

  typedef boost::unordered_set<term_ref, term_ref_hasher> visited_set;

  // The DFS stack
  std::vector<dfs_entry> dfs_stack;

  // Terms already visited
  visited_set v;

  // Add initial one
  dfs_stack.push_back(dfs_entry(t, false, d_visitor.match(t)));

  while (!dfs_stack.empty()) {

    // Process current
    dfs_entry& current = dfs_stack.back();

    // If visited already, we just skip it
    if (v.find(current.t) != v.end()) {
      dfs_stack.pop_back();
      continue;
    }

    // If children added, then we visit this node
    if (current.children_added) {
      if (current.visit == VISIT_AND_BREAK ||
          current.visit == VISIT_AND_CONTINUE) {
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
    if (current.visit == DONT_VISIT_AND_CONTINUE ||
        current.visit == VISIT_AND_CONTINUE) {
      // We should add them
      const term& current_term = d_tm.term_of(current.t);
      for (size_t i = 0; i < current_term.size(); ++ i) {
        dfs_stack.push_back(dfs_entry(current_term[i], false, d_visitor.match(current_term[i])));
      }
    }
  }
}


}
}
