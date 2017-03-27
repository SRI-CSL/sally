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

#include "string.h"
#include <iostream>
#include <string.h>
#include <stdlib.h>

namespace sally {
namespace utils {

string::string()
: d_data(0)
{
}

string::string(const char* data)
: d_data(strdup(data))
{
}

string::string(const string& other)
: d_data(strdup(other.d_data))
{
}

string::string(std::string s)
: d_data(strdup(s.c_str()))
{
}

string::~string()
{
  if (d_data) {
    free(d_data);
  }
}

string& string::operator = (const string& s) {
  if (this != &s) {
    if (d_data) {
      free(d_data);
      d_data = strdup(s.d_data);
    }
  }
  return *this;
}

bool string::operator == (const string& s) const {
  if (d_data == 0 && s.d_data == 0) {
    return true;
  }
  if (d_data == 0 || s.d_data == 0) {
    return false;
  }
  return strcmp(d_data, s.d_data) == 0;
}


const char* string::begin() const {
  return d_data;
}

const char* string::end() const {
  return d_data + size();
}


size_t string::size() const {
  if (d_data) {
    return strlen(d_data);
  } else {
    return 0;
  }
}

char string::operator[] (size_t i) const {
  return d_data[i];
}

const char* string::c_str() const {
  return d_data;
}

string::operator std::string () const {
  return d_data;
}

void string::to_stream(std::ostream& out) const {
  if (d_data) {
    out << d_data;
  }
}

std::ostream& operator << (std::ostream& out, const string& s) {
  s.to_stream(out);
  return out;
}

}
}
