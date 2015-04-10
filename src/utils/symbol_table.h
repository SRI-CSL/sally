/*
 * symbol_table.h
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#pragma once

#include <set>
#include <list>
#include <vector>
#include <boost/unordered_map.hpp>

namespace sally {
namespace utils {

template<typename T, bool free_pointers = true>
class symbol_table {

  typedef std::list<T> T_list;
  typedef typename T_list::iterator T_list_iterator;
  typedef boost::unordered_map<std::string, T_list, utils::hash<std::string> > id_to_T_map;
  typedef typename id_to_T_map::iterator iterator;
  typedef typename id_to_T_map::const_iterator const_iterator;

  template<typename T1>
  struct symbol_table_entry {
    enum { is_pointer = false };
    static void free(T1& t) {}
    static void free(const T1& t) {}
  };

  template<typename T1>
  struct symbol_table_entry<T1*> {
    enum { is_pointer = true };
    static void free(T1* t) { delete t; }
  };

  /** Map from names to lists of entries */
  id_to_T_map d_table;

  /** The added entries */
  std::vector<std::string> d_entries_added;

  /** Number of entries per context push */
  std::vector<size_t> d_entries_added_size_per_push;

  /** Remove an entry id -> value */
  void remove_entry(std::string id) {
    assert(d_table.find(id) != d_table.end());
    assert(d_table[id].size() > 0);
    d_table[id].pop_front();
  }

  /** Name of the symbol table for debugging */
  std::string d_name;

public:

  symbol_table(std::string name)
  : d_name(name)
  {}

  ~symbol_table() {
    if (free_pointers && symbol_table_entry<T>::is_pointer) {
      std::set<T> to_delete;
      for (iterator it = d_table.begin(); it != d_table.end(); ++ it) {
        for (T_list_iterator l_it = it->second.begin(); l_it != it->second.end(); ++ l_it) {
          to_delete.insert(*l_it);
        }
      }
      for (typename std::set<T>::iterator it = to_delete.begin(); it != to_delete.end(); ++ it) {
        symbol_table_entry<T>::free(*it);
      }
    }
  }

  /** Start a new scope */
  void push_scope() {
    d_entries_added_size_per_push.push_back(d_entries_added.size());
  }

  /** Remove top scope */
  void pop_scope() {
    size_t pop_to_size = d_entries_added_size_per_push.back();
    d_entries_added_size_per_push.pop_back();
    while (d_entries_added.size() > pop_to_size) {
      remove_entry(d_entries_added.back());
      d_entries_added.pop_back();
    }
  }

  /** Add an entry id -> value, and return the reference to the table entry */
  void add_entry(std::string id, const T& value) {
    d_table[id].push_front(value);
    d_entries_added.push_back(id);
  }

  /** Get the value associated to id -> value */
  const T& get_entry(std::string id) const {
    const_iterator find = d_table.find(id);
    assert(find != d_table.end());
    const T_list& list = find->second;
    assert(!list.empty());
    return list.front();
  }

  /** Does the id have an entry */
  bool has_entry(std::string id) const {
    const_iterator find = d_table.find(id);
    if (find == d_table.end()) {
      return false;
    }
    const T_list& list = find->second;
    if (list.empty()) {
      return false;
    } else {
      return true;
    }
  }

  /** Print the table to stream */
  void to_stream(std::ostream& out) const {
    out << "[" << d_name << ":";
    for (const_iterator it = d_table.begin(); it != d_table.end(); ++ it) {
      out << " " << it->first << " -> " << it->second.back();
    }
    out << "]";
  }

  template<typename gc_relocator>
  void gc_relocate(const gc_relocator& gc_reloc)  {
    for (iterator it = d_table.begin(); it != d_table.end(); ++ it) {
      typename T_list::iterator t_it = it->second.begin();
      typename T_list::const_iterator t_it_end = it->second.end();
      for (; t_it != t_it_end; ++ t_it) {
        T t = *t_it;
        bool relocated = gc_reloc.reloc(t);
        assert(relocated);
        *t_it = t;
      }
    }
  }

};

template<typename T>
std::ostream& operator << (std::ostream& out, const symbol_table<T>& table) {
  table.to_stream(out);
  return out;
}

}
}
