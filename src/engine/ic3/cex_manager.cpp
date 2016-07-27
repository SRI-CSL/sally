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

#include "cex_manager.h"

#include <iostream>
#include <limits>

using namespace sally;
using namespace ic3;

cex_manager::cex_manager(expr::term_manager& tm)
: d_tm(tm)
{
}

void cex_manager::clear() {
  d_cex_graph.clear();
}

void cex_manager::add_edge(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id) {

  cex_edge new_edge(B, edge_length, property_id);

  // Don't add duplicate edges
  cex_graph::iterator graph_find = d_cex_graph.find(A);
  if (graph_find != d_cex_graph.end()) {
    edge_list& edges = graph_find->second;
    edge_list::iterator it = edges.begin();
    for (; it != edges.end(); ++ it) {
      if (it->B == B && it->property_id == property_id) {
        if (it->edge_length == edge_length) {
          // Already there
          return;
        }
        if (it->edge_length < edge_length) {
          // Smallest one, insert and done
          edges.insert(it, new_edge);
          return;
        }
        if (it->edge_length > edge_length) {
          // Bigger one, insert after
          it++;
          edges.insert(it, new_edge);
          return;
        }
      }
    }
  }

  // Add edge to the graph
  d_cex_graph[A].push_back(new_edge);
}

void cex_manager::mark_root(expr::term_ref A, size_t property_id) {
  d_roots.push_back(cex_root(A, property_id));
}

expr::term_ref cex_manager::get_root(size_t property_id) const {
  for (size_t i = 0; i < d_roots.size(); ++ i) {
    if (d_roots[i].property_id == property_id) {
      return d_roots[i].A;
    }
  }
  return expr::term_ref();
}

cex_manager::cex_edge cex_manager::get_next(expr::term_ref A, size_t property_id) const {
  cex_graph::const_iterator graph_find = d_cex_graph.find(A);
  assert(graph_find != d_cex_graph.end());

  static cex_edge null_edge(expr::term_ref(), 0, 0);

  // Return the first one, we don't really care
  const edge_list& edges = graph_find->second;
  edge_list::const_iterator it = edges.begin();
  for (; it != edges.end(); ++ it) {
    if (property_id == it->property_id) {
      return *it;
    }
  }

  assert(false);
  return cex_edge(expr::term_ref(), std::numeric_limits<size_t>::max(), null_property_id);
}

void cex_manager::to_stream(std::ostream& out) const {

}

std::ostream& operator << (std::ostream& out, const cex_manager& cm) {
  cm.to_stream(out);
  return out;
}


