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

#include <iosfwd>
#include <string>
#include <vector>

#include "utils/hash.h"

namespace sally {
namespace expr {

class enum_value {

  /** Index of the constant */
  size_t d_index;

  /** All values in the type */
  std::vector<std::string> d_values;

public:

  /** Construct 0 of size 1 */
  enum_value(): d_index(0) {}

  /** Copy constructor */
  enum_value(const enum_value& other)
  : d_index(other.d_index), d_values(other.d_values)
  {}

  /** Construct from id and name */
  enum_value(size_t index, const std::vector<std::string>& values)
  : d_index(index), d_values(values)
  {}

  /** Get the size of the bitvector */
  size_t index() const { return d_index; }

  /** Return the name of the constant */
  std::string name() const { return d_values[d_index]; }

  /** Returns all the values in the enumeration */
  const std::vector<std::string> values() const { return d_values; }

  /** Hash */
  size_t hash() const {
    utils::sequence_hash sh;
    sh.add(d_index);
    for (unsigned i = 0; i < d_values.size(); ++ i) {
      sh.add(d_values[i]);
    }
    return sh.get();
  }

  /** Compare */
  bool operator == (const enum_value& other) const {
    if (d_index != other.d_index) {
      return false;
    }
    if (d_values.size() != other.d_values.size()) {
      return false;
    }
    for (unsigned i = 0; i < d_values.size(); ++ i) {
      if (d_values[i] != other.d_values[i]) {
        return false;
      }
    }
    return true;
  }

  /** Output to stream */
  void to_stream(std::ostream& out) const {
    out << d_values[d_index];
  }
};

inline
std::ostream& operator << (std::ostream& out, const enum_value& bv) {
  bv.to_stream(out);
  return out;
}

}

namespace utils {

template<>
struct hash<expr::enum_value> {
  size_t operator()(const expr::enum_value& bv) const {
    return bv.hash();
  }
};

}
}
