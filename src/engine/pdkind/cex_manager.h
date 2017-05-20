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

#include "expr/term.h"
#include "expr/term_map.h"

#include <list>
#include <vector>
#include <iosfwd>

namespace sally {
namespace pdkind {

/**
 * Manager for counter-examples in IC3. It's a graph from counter-example to
 * counter-example.
 *
 * * Each node is a generalization that leads to negation of a property.
 * * Each edge is one path towards the full counterexample and is labeled with
 *   - The property ID
 *   - The depth of the counter-example
 */
class cex_manager {

public:

  /** Null property id */
  static const size_t null_property_id = -1;

  /** Edge to B */
  struct cex_edge {
    expr::term_ref B;
    size_t edge_length, property_id;
    cex_edge(expr::term_ref B, size_t edge_length, size_t property_id)
    : B(B), edge_length(edge_length), property_id(property_id) {}
    cex_edge()
    : edge_length(-1)
    , property_id(-1)
    {}
  };

private:

  /** List of edges */
  typedef std::list<cex_edge> edge_list;

  /** Map from A -> list of edges */
  typedef expr::term_ref_hash_map<edge_list> cex_graph;

  /** The graph */
  cex_graph d_cex_graph;

  /** 
   * A root of the counter-example: a formula A that intersects with
   * the initial states can lead to a counter-example of the property.
   */ 
  struct cex_root {
    expr::term_ref A;
    size_t property_id;
    cex_root(expr::term_ref A, size_t property_id)
    : A(A), property_id(property_id) {}
  };

  /** Root counter-examples for properties */
  std::vector<cex_root> d_roots;

public:

  /**
   * Add a CEX edge. This will increase the reference count of A, and, if
   * the same edge to B is not already present, increase the reference to B.
   */
  void add_edge(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id);

  /** Clear the counter-example graph */
  void clear();

  /** Mark the node as root of a full counter-example */
  void mark_root(expr::term_ref A, size_t property_id);

  /** Vector of edges that is used in get_full_cex */
  typedef std::vector<cex_edge> edge_vector;

  /**
   * Get the (shortest) counter-example for the given property. If the
   * counter-example is g0 -> g1 -> g2 -> ... -> gn, the edges will
   * contain the nodes g1, ..., gn, while the function returns g0.
   */
  expr::term_ref get_full_cex(size_t property_id, edge_vector& edges) const;

  /** Print to stream */
  void to_stream(std::ostream& out) const;

};

std::ostream& operator << (std::ostream& out, const cex_manager& cm);

}
}
