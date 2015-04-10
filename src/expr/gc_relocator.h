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

class gc_info {

public:

  typedef std::map<expr::term_ref, expr::term_ref> relocation_map;

  /** Construct a the gc info for the tm and given relocation map */
  gc_info(term_manager& tm, const relocation_map& gc_reloc);

  // All methods below set remove unused terms and relocate the used ones

  void collect(expr::term_ref& t) const;
  void collect(expr::term_ref_strong& t) const;

  void collect(std::vector<term_ref>& t_vec) const;
  void collect(std::vector<term_ref_strong>& t_vec) const;
  void collect(std::deque<expr::term_ref>& t_deq) const;

  void collect(std::set<term_ref>& t_set) const;
  void collect(std::set<term_ref_strong>& t_set) const;

  void collect(expr::term_manager::substitution_map& t_map) const;

  void collect(utils::symbol_table<expr::term_ref_strong>& t) const;
  void collect(utils::symbol_table<expr::term_ref>& t) const;

  template<typename value>
  void collect(expr::term_ref_map<value>& t_map) const;

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
void gc_info::collect(expr::term_ref_map<value>& t_map) const {

}

template<typename key, typename key_hasher, typename key_eq>
void gc_info::collect(expr::hash_map_to_term_ref<key, key_hasher, key_eq>& to_t_map) const {

}

}
}
