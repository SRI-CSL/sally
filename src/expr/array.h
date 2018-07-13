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
#include <map>

#include "value.h"
#include "utils/hash.h"

namespace sally {
namespace expr {


/**
 * An array is a finite list of mappings and a default value. A
 * mapping is of the form [x_1 ... x_k-1 -> x_k]. Each mapping
 * specifies the value of a specific array element.
 */
class array {

public:
  
  typedef std::map<value, value> value_to_value_map;

private:

  /** Default value (for indices not in the mapping) */
  value d_def_val;

  /** Mapping indices -> values */
  value_to_value_map d_mapping;
    
public:

  array();
  array(const array& a);

  /** Construct the array given default value and the mapping */
  array(const value& def_val, const value_to_value_map& mapping);

  /** Check equality */
  bool operator==(const array& other) const;

  /** Get the hash */
  size_t hash() const;

  /** Write to stream */
  void to_stream(std::ostream& out) const;
};

std::ostream& operator<<(std::ostream& out, const array& a);

}

namespace utils {

template<>
struct hash<expr::array> {
  size_t operator()(const expr::array& a) const {
    return a.hash();
  }
};

}
}
