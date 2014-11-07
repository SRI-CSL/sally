/*
 * symbol_table.h
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#pragma once

#include <list>
#include <vector>
#include <boost/unordered_map.hpp>

namespace sal2 {
namespace utils {

template<typename T>
class symbol_table {

  typedef std::list<T> T_list;
  typedef boost::unordered_map<std::string, T_list, utils::hash<std::string> > id_to_T_map;
  typedef typename id_to_T_map::iterator iterator;


  /** Map from names to lists of entries */
  id_to_T_map d_table;

  /** The added entries */
  std::vector<std::string> d_entries_added;

  /** Number of entries per context push */
  std::vector<size_t> d_entries_added_size_per_push;

  /** Remove an entry id -> value */
  void remove_entry(std::string id) {
    d_table[id].pop_front();
  }

public:

  /** Start a new scope */
  void new_scope() {
    d_entries_added_size_per_push.push_back(d_entries_added.size());
  }

  /** Remove top scope */
  void pop_scope() {
    size_t pop_to_size = d_entries_added_size_per_push.back();
    d_entries_added_size_per_push.pop_back();
    while (d_entries_added.size() >= pop_to_size) {
      remove_entry(d_entries_added.back());
    }
  }

  /** Add an entry id -> value */
  void add_entry(std::string id, const T& value) {
    d_table[id].push_front(value);
    d_entries_added.push_back(id);
  }

  /** Get the value associated to id -> value */
  const T& get_entry(std::string id) const {
    assert(d_table.find(id) != d_table.end(id));
    const T_list& list = d_table.find(id)->second;
    assert(!list.empty());
    return list.front();
  }
};

}
}
