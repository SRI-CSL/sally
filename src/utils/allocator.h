/*
 * allocator.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <cstdlib>

namespace sal2 {
namespace utils {

class allocator {

  /** The memory */
  char* d_memory;

  /** Used memory */
  size_t d_size;

  /** Available memory */
  size_t d_capacity;

public:

  /** Constructor */
  allocator(size_t initial_size = 10000)
  : d_memory(static_cast<char*>(std::malloc(initial_size)))
  , d_size(0)
  , d_capacity(initial_size)
  {}

  ~allocator() {
    std::free(d_memory);
  }

  /** Allocate at least size bytes and return the pointer */
  template<typename T>
  T* allocate(size_t size);

  /** Get the index of object in allocator */
  template<typename T>
  size_t index_of(const T* o) const {
    return (const char*)o - d_memory;
  }

  template<typename T>
  const T& get(size_t i) const { return *((const T*)d_memory + i); }

  template<typename T>
  T& get(size_t i) { return *((T*)d_memory + i); }
};

template<typename T>
T* allocator::allocate(size_t size) {
  // Align the d_size
  size = (size + 7) & ~((size_t)7);

  // Make sure there is enough memory
  size_t requested = d_size + size;
  if (requested > d_capacity) {
    while (requested > d_capacity) {
      d_capacity += d_capacity / 2;
    }
    d_memory = (char*) std::realloc(d_memory, d_capacity);
  }

  // Actually allocate
  T* o = (T*)(d_memory + d_size);
  // Increase the d_size
  d_size  += size;
  // Return the clause memory
  return o;
}

}
}
