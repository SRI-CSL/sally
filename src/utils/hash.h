/*
 * hash.h
 *
 *  Created on: Oct 4, 2014
 *      Author: dejan
 */

#pragma once

#include <string>

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


}
}
