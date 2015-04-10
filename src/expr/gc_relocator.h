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
#include <boost/unordered_map.hpp>

#include "expr/term_manager.h"
#include "expr/term_map.h"
#include "utils/symbol_table.h"

namespace sally {
namespace expr {

class gc_relocator {

public:

  typedef std::map<expr::term_ref, expr::term_ref> relocation_map;

  /** Construct a the gc info for the tm and given relocation map */
  gc_relocator(term_manager& tm, const relocation_map& gc_reloc);

  /** Relocate t to its new value or make it null if collected */
  void collect(expr::term_ref& t) const;

  /** Relocate t to its new value or make it null if collected */
  void collect(expr::term_ref_strong& t) const;

  /** Relocate all terms to their new value and shrink the vector (maintains order) */
  void collect(std::vector<term_ref>& t_vec) const;

  /** Relocate all terms to their new value */
  void collect(std::vector<term_ref_strong>& t_vec) const;

  /** Relocate all terms to their new value and shrink the deque (maintains order) */
  void collect(std::deque<expr::term_ref>& t_deq) const;

  /** Relocate all terms and remove the collected ones */
  void collect(std::set<term_ref>& t_set) const;

  /** Relocate all terms */
  void collect(std::set<term_ref_strong>& t_set) const;

  /** Relocate all terms and remove pairs where some term was collected */
  void collect(expr::term_manager::substitution_map& t_map) const;

  /** Relocate all terms */
  void collect(utils::symbol_table<expr::term_ref_strong>& t) const;

  /** Relocate all terms and remove entries where the terms was collected */
  void collect(utils::symbol_table<expr::term_ref>& t) const;

  /** Relocate all keys and remove keys where term was collected */
  template<typename value>
  void collect(expr::term_ref_map<value>& t_map) const;

  /** Relocate all values and remove keys where value term was collected */
  template<typename key, typename key_hasher, typename key_eq>
  void collect(expr::hash_map_to_term_ref<key, key_hasher, key_eq>& to_t_map) const;

private:

  /** The term manager in charge */
  term_manager& d_tm;

  /**
   * Map from old references to new references. Anything not in the map should
   * be removed.
   */
  const relocation_map& d_relocation_map;

};

template<typename value>
void gc_relocator::collect(expr::term_ref_map<value>& t_map) const {
  expr::term_ref_map<value> new_t_map;
  typename expr::term_ref_map<value>::const_iterator it = t_map.begin(), it_end = t_map.end();
  for (; it != it_end; ++ it) {
    term_ref t = it->first;
    collect(t);
    if (!t.is_null()) {
      new_t_map[t] = it->second;
    }
  }
  t_map.swap(new_t_map);
}

template<typename key, typename key_hasher, typename key_eq>
void gc_relocator::collect(expr::hash_map_to_term_ref<key, key_hasher, key_eq>& to_t_map) const {
  expr::hash_map_to_term_ref<key, key_hasher, key_eq> new_to_t_map;
  typename expr::hash_map_to_term_ref<key, key_hasher, key_eq>::const_iterator it = new_to_t_map.begin(), it_end = new_to_t_map.end();
  for (; it != it_end; ++ it) {
    term_ref t = it->second;
    collect(t);
    if (!t.is_null()) {
      new_to_t_map[it->first] = t;
    }
  }
  to_t_map.swap(new_to_t_map);
}

}
}
