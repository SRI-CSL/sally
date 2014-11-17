/*
 * allocator_types.h
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#pragma once

namespace sal2 {
namespace alloc {

struct empty_type {
  bool operator == (empty_type other) const { return true; }
};

template<typename T>
struct type_traits {
  static const bool is_empty = false;
};

template<>
struct type_traits<empty_type> {
  static const bool is_empty = true;
};

}

namespace utils {

template<>
struct hash<alloc::empty_type> {
  size_t operator()(alloc::empty_type e) const { return 0; }
};

}

namespace alloc {

/**
 * References to the allocated memory, just indices into the memory. There
 * are two special values: the null reference (for default values and bad
 * results) and lazy reference (meant for references not yet allocated).
 */
class ref {
protected:

  /** Index into the memory */
  size_t d_ref;

  ref(size_t ref): d_ref(ref) {}

  /** Allocator can create references */
  friend class allocator_base;

  /** Index for null value */
  static const size_t null_value = (size_t)-1;

public:

  /** Only for descendants */
  size_t index() const { return d_ref; }

  /** Create undefined reference */
  ref(): d_ref(null_value) {}
  /** Copy construct */
  ref(const ref& r): d_ref(r.d_ref) {}

  /** Is this null reference */
  bool is_null() const { return d_ref == null_value; }

  /** Compare */
  bool operator == (const ref& r) const { return d_ref == r.d_ref; }

  /** Compare */
  bool operator != (const ref& r) const { return d_ref != r.d_ref; }
};

}
}
