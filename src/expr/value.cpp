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

#include "value.h"
#include "expr/term_manager.h"

#include <iostream>
#include <cassert>

namespace sally {
namespace expr {

value::value()
: d_type(VALUE_NONE)
, d_b(false)
{
}

value::value(bool b)
: d_type(VALUE_NONE)
, d_b(b)
{
}

value::value(const value& v)
: d_type(v.d_type)
, d_b(v.d_b)
, d_bv(v.d_bv)
, d_q(v.d_q)
{
}

value::value(const rational& q)
: d_type(VALUE_RATIONAL)
, d_b(false)
, d_q(q)
{
}

value::value(const bitvector& bv)
: d_type(VALUE_BITVECTOR)
, d_b(false)
, d_bv(bv)
{
}

value::value(const term_manager& tm, term_ref t)
: d_type(VALUE_NONE)
, d_b(false)
{
  const expr::term& t_term = tm.term_of(t);
  expr::term_op op = t_term.op();
  switch (op) {
  case CONST_BOOL:
    d_b = tm.get_boolean_constant(t_term);
    break;
  case CONST_BITVECTOR:
    d_bv = tm.get_bitvector_constant(t_term);
    break;
  case CONST_RATIONAL:
    d_q = tm.get_rational_constant(t_term);
    break;
  default:
    assert(false);
  }
}

value& value::operator = (const value& v) {
  if (this != &v) {
    d_type = v.d_type;
    d_b = v.d_b;
    d_bv = v.d_bv;
    d_q = v.d_q;
  }
  return *this;
}

bool value::operator == (const value& v) const {

  if (d_type != v.d_type) {
    return false;
  }

  switch (d_type) {
  case VALUE_NONE:
    return true;
  case VALUE_BOOL:
    return d_b == v.d_b;
  case VALUE_BITVECTOR:
    return d_bv == v.d_bv;
  case VALUE_RATIONAL:
    return d_q == v.d_q;
  default:
    return false;
  }
}

bool value::operator != (const value& v) const {
  return !(*this == v);
}

size_t value::hash() const {
  switch (d_type) {
  case VALUE_NONE:
    return 0;
  case VALUE_BOOL:
    return d_b;
  case VALUE_BITVECTOR:
    return d_bv.hash();
  case VALUE_RATIONAL:
    return d_q.hash();
  default:
    return 0;
  }
}

void value::to_stream(std::ostream& out) const {
  switch (d_type) {
  case VALUE_NONE:
    out << "VALUE_NONE";
    break;
  case VALUE_BOOL:
    out << (d_b ? "true" : "false");
    break;
  case VALUE_BITVECTOR:
    out << d_bv;
    break;
  case VALUE_RATIONAL:
    out << d_q;
    break;
  }
}

bool value::get_bool() const {
  assert(is_bool());
  return d_b;
}

const bitvector& value::get_bitvector() const {
  assert(is_bitvector());
  return d_bv;
}

const rational& value::get_rational() const {
  assert(is_rational());
  return d_q;
}

term_ref value::to_term(term_manager& tm) const {
  switch (d_type) {
  case VALUE_NONE:
    return term_ref();
  case VALUE_BOOL:
    return tm.mk_boolean_constant(d_b);
  case VALUE_BITVECTOR:
    return tm.mk_bitvector_constant(d_bv);
  case VALUE_RATIONAL:
    return tm.mk_rational_constant(d_q);
  }
  return term_ref();
}


std::ostream& operator << (std::ostream& out, const value& v) {
  v.to_stream(out);
  return out;
}

}
}
