/*
 * gc_relocator.h
 *
 *  Created on: Apr 9, 2015
 *      Author: dejan
 */

#pragma once

#include <set>
#include <map>
#include <deque>
#include <vector>

#include "expr/term_manager.h"
#include "utils/symbol_table.h"

namespace sally {
namespace expr {

class gc_relocator {

public:

  typedef std::map<expr::term_ref, expr::term_ref> relocation_map;

  /** Construct a the gc info for the tm and given relocation map */
  gc_relocator(term_manager& tm, const relocation_map& gc_reloc);

  /** Relocate t to its new value or make it null if collected. Returns true if relocated, false if collected. */
  bool reloc(expr::term_ref& t) const;

  /** Relocate t to its new value or make it null if collected. Returns true if relocated, false if collected. */
  bool reloc(expr::term_ref_strong& t) const;

  /** Relocate all terms to their new value and shrink the vector (maintains order) */
  void reloc(std::vector<term_ref>& t_vec) const;

  /** Relocate all terms to their new value */
  void reloc(std::vector<term_ref_strong>& t_vec) const;

  /** Relocate all terms to their new value and shrink the deque (maintains order) */
  void reloc(std::deque<expr::term_ref>& t_deq) const;

  /** Relocate all terms and remove the collected ones */
  void reloc(std::set<term_ref>& t_set) const;

  /** Relocate all terms */
  void reloc(std::set<term_ref_strong>& t_set) const;

  /** Relocate all terms and remove pairs where some term was collected */
  void reloc(expr::term_manager::substitution_map& t_map) const;

private:

  /** The term manager in charge */
  term_manager& d_tm;

  /**
   * Map from old references to new references. Anything not in the map should
   * be removed.
   */
  const relocation_map& d_relocation_map;

};

}
}
