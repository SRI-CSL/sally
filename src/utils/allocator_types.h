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

namespace sally {
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
