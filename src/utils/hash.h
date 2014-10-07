/*
 * hash.h
 *
 *  Created on: Oct 4, 2014
 *      Author: dejan
 */

#pragma once

namespace sal2 {

namespace utils {

/**
 * To be instantiated by any type that needs to be hashed by sal. Default hash
 * is just a cast to size_t.
 */
template<typename T>
struct hash {
  size_t operator()(bool value) const {
    return static_cast<size_t>(value);
  }
};

/** Hasher for a sequence of hashes */
class sequence_hash {
  size_t d_hash;
public:
  sequence_hash(): d_hash(0) {}
  void add(size_t h) {
    d_hash ^= h + 0x9e3779b9 + (d_hash << 6) + (d_hash >> 2);
  }
  size_t get() const { return d_hash; }
};

}
}
