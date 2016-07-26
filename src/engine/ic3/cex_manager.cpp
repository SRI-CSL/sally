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
  d_cex_refcount.clear();
}

void cex_manager::add(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id) {

  // Increase the reference count
  d_cex_refcount[A] ++;
  d_cex_refcount[B] ++;

#ifndef NDEBUG
  // Check that the edge is not duplicate
  cex_graph::const_iterator graph_find = d_cex_graph.find(A);
  if (graph_find != d_cex_graph.end()) {
    const edge_list& edges = graph_find->second;
    edge_list::const_iterator it = edges.begin();
    for (; it != edges.end(); ++ it) {
      assert(it->B != B || it->edge_length != edge_length || it->property_id != property_id);
    }
  }
#endif

  // Add edge to the graph
  d_cex_graph[A].push_back(cex_edge(B, edge_length, property_id));
}

void cex_manager::remove_node(expr::term_ref A) {

  assert(d_cex_refcount.find(A) != d_cex_refcount.end() && d_cex_refcount.find(A)->second == 0);
  assert(d_cex_graph.find(A) != d_cex_graph.end() && d_cex_graph.find(A)->second.size() == 0);

  d_cex_refcount.erase(A);
  d_cex_graph.erase(A);
}

void cex_manager::remove(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id) {

  cex_refcount::iterator refcount_find;
  cex_graph::iterator graph_find;

  // Remove from graph
  graph_find = d_cex_graph.find(A);
  assert(graph_find != d_cex_graph.end());
  edge_list& edges = graph_find->second;
  edge_list::iterator edge_find = edges.begin();
  for(; edge_find != edges.end(); ++ edge_find) {
    if (edge_find->B == B && edge_find->edge_length == edge_length && edge_find->property_id == property_id) {
      edges.erase(edge_find);
      break;
    }
  }
  assert(edge_find != edges.end());

  // Decrease the reference count
  refcount_find = d_cex_refcount.find(A);
  assert(refcount_find != d_cex_refcount.end());
  if (-- refcount_find->second == 0) { remove_node(A); }
  refcount_find = d_cex_refcount.find(B);
  assert(refcount_find != d_cex_refcount.end());
  if (-- refcount_find->second == 0) { remove_node(B); }

}

void cex_manager::mark_root(expr::term_ref A, size_t property_id) {
  d_roots.push_back(cex_root(A, property_id));
}

cex_manager::cex_edge cex_manager::get_next(expr::term_ref A, size_t property_id) const {
  cex_graph::const_iterator graph_find = d_cex_graph.find(A);
  assert(graph_find != d_cex_graph.end());

  const edge_list& edges = graph_find->second;
  cex_edge min_edge(expr::term_ref(), std::numeric_limits<size_t>::max(), std::numeric_limits<size_t>::max());

  edge_list::const_iterator it = edges.begin();
  for (; it != edges.end(); ++ it) {
    if (property_id == it->property_id && min_edge.edge_length>= it->edge_length) {
      min_edge = *it;
    }
  }

  return min_edge;
}


void cex_manager::to_stream(std::ostream& out) const {

}

std::ostream& operator << (std::ostream& out, const cex_manager& cm) {
  cm.to_stream(out);
  return out;
}


