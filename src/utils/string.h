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

#include <string>
#include <iosfwd>

namespace sally {
namespace utils {

class string {

  char* d_data;

public:

  string();
  string(const char* data);
  string(const string& s);
  string(std::string s);
  ~string();

  string& operator = (const string& s);
  bool operator == (const string& s) const;

  const char* begin() const;
  const char* end() const;

  size_t size() const;
  char operator[] (size_t i) const;
  const char* c_str() const;

  void to_stream(std::ostream& out) const;

};

std::ostream& operator << (std::ostream& out, const string& s);

}
}
