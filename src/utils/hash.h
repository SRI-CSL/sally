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

#include <string>
#include "utils/string.h"

namespace sally {
namespace utils {

/**
 * To be instantiated by any type that needs to be hashed by sal. Default hash
 * is just a cast to size_t.
 */
template<typename T>
struct hash {
  size_t operator()(T value) const {
    return static_cast<size_t>(value);
  }
};

/** Hasher for a sequence of hashes */
class sequence_hash {
  size_t d_hash;
public:
  sequence_hash(): d_hash(0) {}

  template <typename T>
  void add(const T& t) {
    d_hash ^= hash<T>()(t) + 0x9e3779b9 + (d_hash << 6) + (d_hash >> 2);
  }
  size_t get() const { return d_hash; }

  template <typename iterator>
  void add(iterator begin, iterator end) {
    for (; begin != end; ++ begin) {
      add(*begin);
    }
  }
};

/** String hash. */
template<>
struct hash<std::string> {
  size_t operator()(std::string value) const {
    sequence_hash seq;
    seq.add(value.begin(), value.end());
    return seq.get();
  }
};

/** String hash. */
template<>
struct hash<utils::string> {
  size_t operator()(utils::string value) const {
    sequence_hash seq;
    seq.add(value.begin(), value.end());
    return seq.get();
  }
};

}
}
