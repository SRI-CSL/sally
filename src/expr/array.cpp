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

#include <iostream>
#include <cassert>
#include <sstream>
#include "array.h"
#include "term.h"
#include "value.h"

#include "utils/output.h"


namespace sally {
namespace expr {

array::array()
{}

array::array(const array& a)
: d_def_val(a.d_def_val)
, d_mapping(a.d_mapping)
, d_type(a.d_type)  
{}

array::array(const value& def_val, const value_to_value_map& mapping, term_ref type)
: d_def_val(def_val)
, d_mapping(mapping)
, d_type(type)  
{}

bool array::operator==(const array& other) const {
  // ignore d_type for comparison
  if (d_def_val != other.d_def_val) {
    return false;
  }
  
  if (d_mapping.size() != other.d_mapping.size()) {
    return false;
  }

  return std::equal(d_mapping.begin(), d_mapping.end(), other.d_mapping.begin());
}

bool array::operator < (const array& other) const {
  if (d_def_val != other.d_def_val) {
    return d_def_val < other.d_def_val;
  }

  return std::lexicographical_compare(d_mapping.begin(), d_mapping.end(),
      other.d_mapping.begin(), other.d_mapping.end());
}


size_t array::hash() const {
  // ignore d_type for computing the hash
  utils::sequence_hash hasher;
  hasher.add(d_def_val.hash());

  value_to_value_map::const_iterator it = d_mapping.begin();
  for (; it != d_mapping.end(); ++ it) {
    hasher.add(it->first);
    hasher.add(it->second);
  }

  return hasher.get();
}

template <typename T>  
static std::string to_str(T x, std::ostringstream &out) {
  out << x;
  std::string res = out.str();
  // clear out
  out.str("");
  out.clear();
  return res;
}

void array::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  switch (lang) {
  case output::MCMT:
  case output::HORN: {
    assert (!d_def_val.is_null());

    expr::term_manager* tm = output::get_term_manager(out);
    std::ostringstream oss;
    output::set_output_language(oss, lang);
    output::set_term_manager(oss, tm);
    
    std::string str;
    str = "((as const " + to_str(d_type, oss)  + ") " + to_str(d_def_val, oss) + ")";
    value_to_value_map::const_iterator it = d_mapping.begin();
    for (; it != d_mapping.end(); ++ it) {
      str = "(store " + str + " " + to_str(it->first, oss) + " " + to_str(it->second, oss) + ")";
    }
    out << str;
    break;
  }
  case output::NUXMV:
  default:
    assert(false);
  }
}

std::ostream& operator << (std::ostream& out, const array& a) {
  a.to_stream(out);
  return out;
}

}

namespace utils {

template<>
struct hash<expr::value> {
  size_t operator()(const expr::value& v) const {
    return v.hash();
  }
};

}


}
