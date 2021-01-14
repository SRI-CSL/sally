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
#include "expr/algebraic_number.h"
#include "expr/enum_value.h"

namespace sally {
namespace expr {

class term_manager;
class term_ref;

class value {

public:

  enum type {
    VALUE_NONE,
    VALUE_BOOL,
    VALUE_RATIONAL,
    VALUE_ALGEBRAIC,
    VALUE_BITVECTOR,
    VALUE_ENUM
  };

private:

  type d_type;

  bool d_b;
  bitvector d_bv;
  rational d_q;
  algebraic_number d_a;
  enum_value d_ev;

public:

  value();
  value(const value& v);
  value(bool b);
  value(const rational& q);
  value(const algebraic_number& a);
  value(const bitvector& bv);
  value(const enum_value& ev);
  value(const term_manager& tm, term_ref t);

  value& operator = (const value& v);

  bool operator == (const value& v) const;
  bool operator != (const value& v) const;

  size_t hash() const;

  void to_stream(std::ostream& out) const;

  type value_type() const { return d_type; }

  bool is_null() const { return d_type == VALUE_NONE; }
  bool is_bool() const { return d_type == VALUE_BOOL; }
  bool is_bitvector() const { return d_type == VALUE_BITVECTOR; }
  bool is_rational() const { return d_type == VALUE_RATIONAL; }
  bool is_algebraic() const { return d_type == VALUE_ALGEBRAIC; }
  bool is_enum_value() const { return d_type == VALUE_ENUM; }

  bool get_bool() const;
  const bitvector& get_bitvector() const;
  const rational& get_rational() const;
  const algebraic_number& get_algebraic() const;
  const enum_value& get_enum_value() const;

  value floor() const;
  bool is_integer() const;

  value operator + (const value& other) const;
  value& operator += (const value& other);

  value operator - () const;
  value operator - (const value& other) const;
  value& operator -= (const value& other);

  value operator * (const value& other) const;
  value& operator *= (const value& other);

  value operator / (const value& other) const;
  value& operator /= (const value& other);

  bool operator < (const value& other) const;
  bool operator <= (const value& other) const;
  bool operator > (const value& other) const;
  bool operator >= (const value& other) const;

  int cmp(const value& other) const;

  term_ref to_term(term_manager& tm) const;
};

std::ostream& operator << (std::ostream& out, const value& v);

}
}
