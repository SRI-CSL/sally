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

#include "expr/bitvector.h"
#include "expr/rational.h"

namespace sally {
namespace expr {

class term_manager;
class term_ref;

class value {

  enum type {
    VALUE_NONE,
    VALUE_BOOL,
    VALUE_RATIONAL,
    VALUE_BITVECTOR,
	VALUE_QUANTIFIED
  };

  type d_type;

  bool d_b;
  bitvector d_bv;
  rational d_q;
  int d_i;

public:

  value();
  value(const value& v);
  value(bool b);
  value(const rational& q);
  value(const bitvector& bv);
  value(const term_manager& tm, term_ref t);
  value(int i);

  value& operator = (const value& v);

  bool operator == (const value& v) const;
  bool operator != (const value& v) const;

  size_t hash() const;

  void to_stream(std::ostream& out) const;

  bool is_null() const { return d_type == VALUE_NONE; }
  bool is_bool() const { return d_type == VALUE_BOOL; }
  bool is_bitvector() const { return d_type == VALUE_BITVECTOR; }
  bool is_rational() const { return d_type == VALUE_RATIONAL; }
  bool is_quantified() const { return d_type == VALUE_QUANTIFIED; }

  bool get_bool() const;
  const bitvector& get_bitvector() const;
  const rational& get_rational() const;
  int get_integer() const;

  term_ref to_term(term_manager& tm) const;
};

std::ostream& operator << (std::ostream& out, const value& v);

}
}
