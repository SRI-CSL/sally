/*
 * hash.h
 *
 *  Created on: Oct 4, 2014
 *      Author: dejan
 */

#pragma once

namespace sal2 {
namespace utils {

class hasher {
  size_t d_hash;
public:
  hasher(): d_hash(0) {}
  void add(size_t x) {
    d_hash ^= x + 0x9e3779b9 + (d_hash << 6) + (d_hash >> 2);
  }
  size_t get() const { return d_hash; }
};

}
}
