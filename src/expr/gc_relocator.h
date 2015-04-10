/*
 * gc_relocator.h
 *
 *  Created on: Apr 9, 2015
 *      Author: dejan
 */

#pragma once

#include <boost/unordered_map.hpp>

#include "expr/term_manager.h"
#include "utils/symbol_table.h"

#include <map>

namespace sally {
namespace expr {

class gc_info {

public:

  typedef std::map<expr::term_ref, expr::term_ref> relocation_map;

  /** Construct a the gc info for the tm and given relocation map */
  gc_info(term_manager& tm, const relocation_map& gc_reloc);

  // All methods below set remove unused terms and relocate the used ones

  void collect(expr::term_ref& t) const;
  void collect(expr::term_ref_strong& t) const;

  /** Removes from linear collections, returns number of removed elements */
  template<typename iterator>
  size_t collect(iterator begin, iterator end) const;

  // MAPS

  size_t collect(expr::term_manager::substitution_map& t_map) const;

  // SYMBOL TABLES (never erase anything), jusr rename

  void collect(utils::symbol_table<expr::term_ref_strong>& t) const;
  void collect(utils::symbol_table<expr::term_ref>& t) const;


private:

  /** The term manager in charge */
  term_manager& d_tm;

  /**
   * Map from old references to new references. Anything not in the map should
   * be removed.
   */
  const relocation_map& d_relocation_map;

};

template<typename iterator>
size_t gc_info::collect(iterator begin, iterator end) const {
  size_t removed = 0;
  for (; begin != end; ++ begin) {
    *begin = collect(*begin);
    if ((*begin).is_null()) {
      removed ++;
    }
  }
  return removed;
}

}
}
