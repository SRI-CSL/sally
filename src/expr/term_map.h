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

#include <map>
#include <boost/unordered_map.hpp>
#include <functional>

namespace sally {
namespace expr {

/** Map from terms to values */
template <typename value>
class term_ref_map : public std::map<term_ref, value> {

  typedef std::map<term_ref, value> super;

public:

  /** Relocate the terms with the given relocator */
  template <typename gc_relocator>
  void reloc(const gc_relocator& gc_reloc) {
    term_ref_map new_t_map;
    typename super::const_iterator it = super::begin();
    typename super::const_iterator it_end = super::end();
    for (; it != it_end; ++ it) {
      term_ref t = it->first;
      bool relocated = gc_reloc.reloc(t);
      if (relocated) {
        new_t_map[t] = it->second;
      }
    }
    super::swap(new_t_map);
  }

};

/** Map from terms to values */
template <typename value>
class term_ref_hash_map : public boost::unordered_map<expr::term_ref, value, expr::term_ref_hasher> {

  typedef boost::unordered_map<expr::term_ref, value, expr::term_ref_hasher> super;

public:

  /** Relocate the terms and remove values that have been collected */
  template <typename gc_relocator>
  void reloc(const gc_relocator& gc_reloc) {
    term_ref_hash_map new_t_map;
    typename super::const_iterator it = super::begin();
    typename super::const_iterator it_end = super::end();
    for (; it != it_end; ++ it) {
      term_ref t = it->first;
      bool relocated = gc_reloc.reloc(t);
      if (relocated) {
        new_t_map[t] = it->second;
      }
    }
    super::swap(new_t_map);
  }

};

/** Map from keys to terms */
template <typename key, typename key_hasher, typename key_eq = std::equal_to<key> >
class hash_map_to_term_ref : public boost::unordered_map<key, expr::term_ref, key_hasher, key_eq> {

  typedef boost::unordered_map<key, expr::term_ref, key_hasher, key_eq> super;

public:

  /** Relocate the terms and remove keys that have been collected */
  template <typename gc_relocator>
  void reloc(const gc_relocator& gc_reloc) {
    hash_map_to_term_ref new_to_t_map;
    typename super::const_iterator it = super::begin();
    typename super::const_iterator it_end = super::end();
    for (; it != it_end; ++ it) {
      term_ref t = it->second;
      bool relocated = gc_reloc.reloc(t);
      if (relocated) {
        new_to_t_map[it->first] = t;
      }
    }
    super::swap(new_to_t_map);
  }

};


}
}
