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

#include <set>
#include <list>
#include <vector>
#include <boost/unordered_map.hpp>

namespace sally {
namespace utils {

/**
 * Symbol table from strings to T. T should be comparable.
 */
template<typename T, bool free_pointers = true>
class symbol_table {

public:

  typedef std::list<T> T_list;
  typedef typename T_list::iterator T_list_iterator;
  typedef boost::unordered_map<std::string, T_list, utils::hash<std::string> > id_to_T_map;
  typedef typename id_to_T_map::iterator iterator;
  typedef typename id_to_T_map::const_iterator const_iterator;

private:

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

  /** The added values */
  std::vector<T> d_values_added;

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
    assert(d_entries_added.size() == d_values_added.size());
  }

  /** Remove top scope */
  void pop_scope() {
    size_t pop_to_size = d_entries_added_size_per_push.back();
    d_entries_added_size_per_push.pop_back();
    while (d_entries_added.size() > pop_to_size) {
      remove_entry(d_entries_added.back());
      d_entries_added.pop_back();
      d_values_added.pop_back();
    }
    assert(d_entries_added.size() == d_values_added.size());
  }

  /** Get the objects in the last scope */
  template <typename collection>
  void get_scope_values(collection& out) {
    std::insert_iterator<collection> insert(out, out.end());
    size_t i = d_entries_added_size_per_push.back();
    for (; i < d_values_added.size(); ++ i) {
      *insert = d_values_added[i];
    }
  }

  /** Add an entry id -> value, and return the reference to the table entry */
  void add_entry(std::string id, const T& value) {
    d_table[id].push_front(value);
    d_entries_added.push_back(id);
    d_values_added.push_back(value);
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

  /** Load variables from another table (only the current ones, not the over-written ones) */
  void load_from(const symbol_table& other) {
    const_iterator it = other.begin(), end = other.end();
    for (; it != end; ++ it) {
      std::string id = it->first;
      const T& value = it->second.front();
      add_entry(id, value);
    }
  }

  const_iterator begin() const { return d_table.begin(); }
  const_iterator end() const { return d_table.end(); }

  /** Print the table to stream */
  void to_stream(std::ostream& out) const {
    out << "[" << d_name << ":";
    for (const_iterator it = d_table.begin(); it != d_table.end(); ++ it) {
      out << " " << it->first << " -> " << it->second.front();
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
        (void)(relocated); // unused var
        assert(relocated);
        *t_it = t;
      }
    }
  }

  size_t size() const {
    return d_table.size();
  }
};

template<typename T>
std::ostream& operator << (std::ostream& out, const symbol_table<T>& table) {
  table.to_stream(out);
  return out;
}

}
}
