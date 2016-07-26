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
#include "expr/term_manager.h"
#include "expr/term_map.h"

#include <list>
#include <iosfwd>

namespace sally {
namespace ic3 {

/**
 * Manager for counter-examples in IC3. It's a graph from counter-example to
 * counter-example.
 *
 * * Each node is a generalization that leads to negation of a property.
 * * Each edge is one path towards the full counterexample and is labeled with
 *   - The property ID
 *   - The depth of the counter-example
 *
 * Nodes are reference-counted and removed when not in use.
 */
class cex_manager {

public:

  /** Edge to B */
  struct cex_edge {
    expr::term_ref B;
    size_t edge_length, property_id;
    cex_edge(expr::term_ref B, size_t edge_length, size_t property_id)
    : B(B), edge_length(edge_length), property_id(property_id) {}
  };

private:

  /** The term manager */
  expr::term_manager& d_tm;

  /** List of edges */
  typedef std::list<cex_edge> edge_list;

  /** Map from A -> list of edges */
  typedef expr::term_ref_hash_map<edge_list> cex_graph;

  /** Reference counts */
  typedef expr::term_ref_hash_map<size_t> cex_refcount;

  /** The graph */
  cex_graph d_cex_graph;

  /** The reference counts */
  cex_refcount d_cex_refcount;

  /** Remove node */
  void remove_node(expr::term_ref A);

  struct cex_root {
    expr::term_ref A;
    size_t property_id;
    cex_root(expr::term_ref A, size_t property_id)
    : A(A), property_id(property_id) {}
  };

  /** Root counter-examples for properties */
  std::vector<cex_root> d_roots;

public:

  /** Create the manager */
  cex_manager(expr::term_manager& tm);

  /** Add a CEX edge */
  void add(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id);

  /** Remove a CEX edge */
  void remove(expr::term_ref A, expr::term_ref B, size_t edge_length, size_t property_id);

  /** Clear the counter-example graph */
  void clear();

  /** Mark the node as root of a full counter-example */
  void mark_root(expr::term_ref A, size_t property_id);

  /** Get the next element of the counter-example (shortest) */
  cex_edge get_next(expr::term_ref A, size_t property_id) const;

  /** Print to stream */
  void to_stream(std::ostream& out) const;

};

std::ostream& operator << (std::ostream& out, const cex_manager& cm);

}
}
