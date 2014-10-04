/*
 * allocator.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <cstdlib>
#include <vector>

namespace sal2 {
namespace utils {

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

  template<typename T>
  size_t index_of(const T* o) const {
    return (const char*)o - d_memory;
  }

  template<typename T>
  ref get_ref(const T* o) { return ref(index_of(o)); }

  template<typename T>
  const T& get(ref o_ref) const { return *((const T*)(d_memory + o_ref.d_ref)); }

  template<typename T>
  T& get(ref o_ref) { return *((T*)d_memory + o_ref.d_ref); }
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

class empty_type {};

template<typename T>
struct type_traits {
  static const bool is_empty = false;
};

template<>
struct type_traits<empty_type> {
  static const bool is_empty = false;
};

template<typename T, typename E = empty_type>
class allocator : public allocator_base {
public:

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
  };

  // All the allocated data
  std::vector<allocator_base::ref> d_allocated;

public:

  /** Allocate T with n children of type E */
  T* allocate(size_t n = 0) {
    data* full;
    if (type_traits<E>::is_empty) {
      full = allocator_base::allocate<data>(sizeof(data));
    } else {
      full = allocator_base::allocate<data>(sizeof(data) + n*sizeof(E));
      full->e_size = n;
    }
    return &full->t_data;
  }

  /** Get the reference of the object */
  ref get_ref(const T& o) const { return ref(allocator_base::index_of<T>(&o)); }

  /** Get the object given the reference */
  const T& get(ref o_ref) const {
    const data& d = allocator_base::get<data>(o_ref);
    return d.t_data;
  }

  /** Get the object given the reference */
  T& get(ref o_ref) {
    const data* data = allocator_base::get<data>(o_ref);
    return data->t_data;
  }

  /** Get the number of children */
  size_t get_size(const T& o) {
    const data* data = allocator_base::get<data>(get_ref(o));
    return data->e_size;
  }

  /** Get the first child */
  const E* begin(const T& o) const {
    const data* data = allocator_base::get<data>(get_ref(o));
    return data->e_data;
  }

  /** Get the last child */
  const E* end(const T& o) const {
    const data* data = allocator_base::get<data>(get_ref(o));
    return data->e_data + data->e_size;
  }

  ~allocator() {
    for (unsigned i = 0; i < d_allocated.size(); ++ i) {
      allocator_base::ref o_ref = d_allocated[i];
      data& d = allocator_base::get<data>(o_ref);
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
