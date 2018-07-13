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

#include <iostream>
#include <cassert>

#include "array.h"
#include "term.h"
#include "value.h"

#include "utils/output.h"


namespace sally {
namespace expr {

array::array()
{}

array::array(const array& a)
: d_def_val(a.d_def_val)
, d_mapping(a.d_mapping)
{}

array::array(const value& def_val, const value_to_value_map& mapping)
: d_def_val(def_val)
, d_mapping(mapping)
{}

bool array::operator==(const array& other) const {

  if (d_def_val != other.d_def_val) {
    return false;
  }
  
  if (d_mapping.size() != other.d_mapping.size()) {
    return false;
  }

  return std::equal(d_mapping.begin(), d_mapping.end(), other.d_mapping.begin());
}

bool array::operator < (const array& other) const {
  if (d_def_val != other.d_def_val) {
    return d_def_val < other.d_def_val;
  }

  return std::lexicographical_compare(d_mapping.begin(), d_mapping.end(),
      other.d_mapping.begin(), other.d_mapping.end());
}


size_t array::hash() const {

  utils::sequence_hash hasher;
  hasher.add(d_def_val.hash());

  value_to_value_map::const_iterator it = d_mapping.begin();
  for (; it != d_mapping.end(); ++ it) {
    hasher.add(it->first);
    hasher.add(it->second);
  }

  return hasher.get();
}

void array::to_stream(std::ostream& out) const {

  if (d_def_val.is_null()) {
    out << "[]";
    return;
  }

  utils::sequence_hash hasher;

  out << "[";
  value_to_value_map::const_iterator it = d_mapping.begin();
  for (; it != d_mapping.end(); ++ it) {
    out << it->first << " -> " << it->second << ", ";
  }
  out << "else -> " << d_def_val << "]";
}
  
std::ostream& operator << (std::ostream& out, const array& a) {
  a.to_stream(out);
  return out;
}

}

namespace utils {

template<>
struct hash<expr::value> {
  size_t operator()(const expr::value& v) const {
    return v.hash();
  }
};

}


}
