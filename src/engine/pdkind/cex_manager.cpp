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

#include <boost/heap/fibonacci_heap.hpp>

#include "utils/trace.h"

namespace sally {
namespace pdkind {

void cex_manager::clear() {
  d_cex_graph.clear();
}

void cex_manager::add_edge(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id) {

  TRACE("pdkind::cex") << "cex_manager: adding edge " << A << " -> " << B << " of length " << edge_length << std::endl;

  cex_edge new_edge(B, edge_length, property_id);

  // Be careful not to add duplicate edges
  cex_graph::iterator graph_find = d_cex_graph.find(A);
  if (graph_find != d_cex_graph.end()) {
    edge_list& edges = graph_find->second;
    edge_list::iterator it = edges.begin();
    for (; it != edges.end(); ++ it) {
      if (it->B == B && it->property_id == property_id) {
        it->edge_length = std::min(edge_length, it->edge_length);
        return;
      }
    }
  }
  
  // Add new edge to the graph
  d_cex_graph[A].push_back(new_edge);
}

void cex_manager::mark_root(expr::term_ref A, size_t property_id) {
  TRACE("pdkind::cex") << "cex_manager: adding root " << A << std::endl;
  d_roots.push_back(cex_root(A, property_id));
}

const size_t infty = -1;

/** Comparison for Dijkstra, comapre based on shortest paths */
class dijkstra_cmp {
  const expr::term_ref_hash_map<size_t>& dist;
public:

  bool operator() (expr::term_ref A, expr::term_ref B) const {

    expr::term_ref_hash_map<size_t>::const_iterator find_A = dist.find(A);
    expr::term_ref_hash_map<size_t>::const_iterator find_B = dist.find(B);

    size_t dist_A = find_A == dist.end() ? infty : find_A->second;
    size_t dist_B = find_B == dist.end() ? infty : find_B->second;

    // Boost has max heaps, so we reverse the order

    if (dist_A == dist_B) { return A > B; }
    else return dist_A > dist_B;
  }

  dijkstra_cmp(const expr::term_ref_hash_map<size_t>& dist)
  : dist(dist) {}
};

/** Previous node information, i.e. A -> B */
struct prev_info {
  
  /** Previous node (A) */
  expr::term_ref node;
  /** The edge taken (-> B) */
  cex_manager::cex_edge edge;

  /** Constructors */
  prev_info() {}
  prev_info(expr::term_ref node, cex_manager::cex_edge edge)
  : node(node), edge(edge) {}
};

expr::term_ref cex_manager::get_full_cex(size_t property_id, edge_vector& edges) const {

  // Q: priority queue
  // dist: distance from a source to the node
  // prev: previous node in the shortest path
  // handle: handle of the node in the priority queue

  typedef boost::heap::fibonacci_heap<expr::term_ref, boost::heap::compare<dijkstra_cmp> > sp_queue;
  typedef sp_queue::handle_type sp_queue_handle;

  expr::term_ref_hash_map<size_t> dist;
  expr::term_ref_hash_map<prev_info> prev;
  expr::term_ref_hash_map<sp_queue_handle> handle;

  dijkstra_cmp cmp(dist);
  sp_queue Q(cmp);

  // Mark all roots as sources
  for (size_t i = 0; i < d_roots.size(); ++ i) {
    if (d_roots[i].property_id == property_id) {
      expr::term_ref A = d_roots[i].A;
      dist[A] = 0;
      handle[A] = Q.push(A);
    }
  }

  // The (negation of the) property
  expr::term_ref property;

  // Dijkstra loop
  while (!Q.empty()) {
    // Next node A to consider
    expr::term_ref A = Q.top();
    Q.pop();

    TRACE("pdkind::cex") << "cex_manger: dijkstra extending from " << A << "." << std::endl;

    // Distance from source to A (we only push distanced nodes to Q)
    expr::term_ref_hash_map<size_t>::iterator dist_it = dist.find(A);
    assert(dist_it != dist.end());
    size_t A_dist = dist_it->second;
    assert(A_dist != infty);

    // Process the children
    const cex_graph::const_iterator graph_it = d_cex_graph.find(A);
    if (graph_it != d_cex_graph.end()) {
      // All edges from A
      const edge_list& edges = graph_it->second;
      // Iterate through edges A -> B
      edge_list::const_iterator edge = edges.begin();
      for (; edge != edges.end(); ++ edge) {
        if (edge->property_id == property_id) {
          // Neighbor 
          expr::term_ref B = edge->B;
          TRACE("pdkind::cex") << "cex_manger: trying edge to " << B << "." << std::endl;
          // Neighbor distance
          dist_it = dist.find(B);
          size_t B_dist = dist_it == dist.end() ? infty : dist_it->second;
          // If distance is 0 then B is the property
          if (edge->edge_length == 0) {
            TRACE("pdkind::cex") << "cex_manger: path to " << B << " found." << std::endl;
            property = B;
            break;
          }
          // Potential new distance
          size_t new_dist = A_dist + edge->edge_length;
          // If better, then update
          if (B_dist == infty)  {
            // Either update, or add new if not there
            if (dist_it != dist.end()) { dist_it->second = new_dist; }
            else { dist[B] = new_dist; }
            // Previous of B is set to A, with the given edge
            prev[B] = prev_info(A, *edge);
            // Add to the queue (we went from inf to not inf, so it's not there yet)
            handle[B] = Q.push(B);
          } else if (new_dist < B_dist) {
            dist_it->second = new_dist;
            // Previous of B is set to A, with the given edge
            prev[B] = prev_info(A, *edge);
            // Since we're updating it must be that we haven't processed it yet
            Q.increase(handle[B]);
          }
        }
      }
    }
  }

  if (property.is_null()) {
    // No path found
    return expr::term_ref();
  }

  // Reconstruct the path
  TRACE("pdkind::cex") << "cex_manger: reconstructing path." << std::endl;
  expr::term_ref current = property;
  for(;;) {
    TRACE("pdkind::cex") << "cex_manger: current = " << current << std::endl;
    const expr::term_ref_hash_map<prev_info>::const_iterator prev_find = prev.find(current);
    if (prev_find == prev.end()) {
      break; // We found the path
    }
    edges.push_back(prev_find->second.edge);
    current = prev_find->second.node;
  }

  // Revers the path and return the source
  std::reverse(edges.begin(), edges.end());
  return current;
}

void cex_manager::to_stream(std::ostream& out) const {

  cex_graph::const_iterator v_it; 
  
  out << "digraph pdkind {" << std::endl;
  out << "  rankdir=LR;" << std::endl;
  out << std::endl;

  // Mark the roots
  out << "  node [shape = doublecircle];" << std::endl;
  for (size_t i = 0; i < d_roots.size(); ++ i) {
    expr::term_ref v = d_roots[i].A;
    out << "  node_" << v.index() << ";" << std::endl;
  }
  out << std::endl;

  // Define the nodes 
  out << "  node [shape = circle];" << std::endl;
  for (v_it = d_cex_graph.begin(); v_it != d_cex_graph.end(); ++ v_it) {
    // Print the node
    expr::term_ref v = v_it->first;
    out << "  node_" << v.index() << ";" << std::endl;
  }
  out << std::endl;

  // Print the graph edges
  for (v_it = d_cex_graph.begin(); v_it != d_cex_graph.end(); ++ v_it) {
    // Print the list of edges
    const edge_list& A_edges = v_it->second;
    edge_list::const_iterator e_it = A_edges.begin();
    for (; e_it != A_edges.end(); ++ e_it) {
      out << "  node_" << v_it->first.index() << " -> ";
      out << "node_" << e_it->B.index() << "[label = \"" << e_it->edge_length << "\"];" << std::endl;
    }
    
    // New one
    out << std::endl;
  }

  out << "}" << std::endl;
}

std::ostream& operator << (std::ostream& out, const cex_manager& cm) {
  cm.to_stream(out);
  return out;
}

}
}