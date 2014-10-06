/*
 * allocator.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <cstdlib>
#include <vector>

#include "utils/hash.h"

namespace sal2 {
namespace alloc {

class empty_type {};
typedef const empty_type* empty_type_ptr;
static const empty_type empty;

template<typename T>
struct type_traits {
  static const bool is_empty = false;
};

template<>
struct type_traits<empty_type> {
  static const bool is_empty = true;
};

}

namespace hash {

template<>
struct hash<alloc::empty_type> {
  size_t operator()(alloc::empty_type e) const { return 0; }
};

}

namespace alloc {
class allocator_base {

  /** The memory */
  char* d_memory;

  /** Used memory */
  size_t d_size;

  /** Available memory */
  size_t d_capacity;

public:

  class ref {
  protected:
    size_t d_ref;
    ref(size_t ref): d_ref(ref) {}
    friend class allocator_base;
  public:
    ref(): d_ref(-1) {}
    ref(const ref& r): d_ref(r.d_ref) {}
    static const ref null;
    int cmp(ref r) const { return d_ref - r.d_ref; }
  };

  /** Constructor */
  allocator_base(size_t initial_size = 10000)
  : d_memory(static_cast<char*>(std::malloc(initial_size)))
  , d_size(0)
  , d_capacity(initial_size)
  {}

  /** Destructor just frees the memory, stuff inside needs to be destructed by hand */
  virtual ~allocator_base() {
    std::free(d_memory);
  }

  /** Allocate at least size bytes and return the pointer */
  template<typename T>
  T* allocate(size_t size);

  /** Returns the index in memory of the given object */
  template<typename T>
  size_t index_of(const T& o) const {
    return (const char*)&o - d_memory;
  }

  /** Returns the reference of the given object */
  template<typename T>
  ref ref_of(const T& o) { return ref(index_of(o)); }

  /** Returns the object pointed to by the given reference */
  template<typename T>
  const T& object_of(ref o_ref) const { return *((const T*)(d_memory + o_ref.d_ref)); }

  /** Returns the object pointed to by the given reference */
  template<typename T>
  T& object_of(ref o_ref) { return *((T*)(d_memory + o_ref.d_ref)); }
};

template<typename T>
T* allocator_base::allocate(size_t size) {

  // Align the size
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
  d_size += size;
  // Return the clause memory
  return o;
}

/**
 * Allocator of objects that have a structure as
 *
 *  - T data
 *  - size_t size
 *  - E elements
 *
 * In other words, the object consist of initial data, and then an inlined
 * array of elements with the size fixed. To ommit the trailing array, just
 * use empty_type for E.
 */
template<typename T, typename E = empty_type>
class allocator : public allocator_base {
public:

  /**
   * The reference class for the <T, E> type of objects.
   */
  class ref : public allocator_base::ref {
    friend class allocator<T, E>;
    ref(size_t ref): allocator_base::ref(ref) {}
  public:
    ref(): allocator_base::ref(-1) {}
    ref(const allocator_base::ref ref): allocator_base::ref(ref) {}
    static const ref null;
  };

private:

  struct data {
    T t_data;
    size_t e_size;
    E e_data[];

    template <typename iterator>
    void construct(const T& data, iterator begin, iterator end) {
      new (&t_data) T(data);
      if (!type_traits<E>::is_empty && begin != end) {
        for (E* e = e_data; begin != end; ++ begin, ++ e) {
          new (e) E(*begin);
        }
      }
    }
  };

  /** All the allocated objects, so that we can destruct it later */
  std::vector<allocator_base::ref> d_allocated;

public:

  /** Allocate T with children from begin .. end */
  template<typename iterator>
  ref allocate(const T& t, iterator begin, iterator end) {
    data* full;
    if (type_traits<E>::is_empty) {
      full = allocator_base::allocate<data>(sizeof(T));
    } else {
      size_t size = end - begin;
      full = allocator_base::allocate<data>(sizeof(data) + size*sizeof(E));
      full->e_size = size;
    }
    full->construct(t, begin, end);
    ref t_ref(allocator_base::index_of(*full));
    d_allocated.push_back(t_ref);
    return t_ref;
  }

  /** Get the reference of the object */
  ref ref_of(const T& o) const { return ref(allocator_base::index_of(o)); }

  /** Get the object given the reference */
  const T& object_of(ref o_ref) const {
    const data& d = allocator_base::object_of<data>(o_ref);
    return d.t_data;
  }

  /** Get the object given the reference */
  T& object_of(ref o_ref) {
    data& d = allocator_base::object_of<data>(o_ref);
    return d.t_data;
  }

  /** Get the number of children */
  size_t object_size(const T& o) const {
    const data& d = (const data&) o;
    return d.e_size;
  }

  /** Get the first child */
  const E* object_begin(const T& o) const {
    const data& d = (const data&) o;
    return d.e_data;
  }

  /** Get the last child */
  const E* object_end(const T& o) const {
    const data& d = (const data&) o;
    return d.e_data + d.e_size;
  }

  /** Destructor, destructs all Ts and Es */
  ~allocator() {
    for (unsigned i = 0; i < d_allocated.size(); ++ i) {
      allocator_base::ref o_ref = d_allocated[i];
      data& d = allocator_base::object_of<data>(o_ref);
      // Destruct Es
      if (!type_traits<E>::is_empty) {
        for (unsigned i = 0; i < d.e_size; ++ i) {
         d.e_data[i].~E();
        }
      }
      // Destruct T
      d.t_data.~T();
    }
  }

};

}
}
