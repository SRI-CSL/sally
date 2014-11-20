/*
 * term.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/term_manager_internal.h"
#include "utils/allocator.h"
#include "utils/output.h"

#include <iomanip>
#include <cassert>
#include <sstream>

namespace sal2 {
namespace expr {

/**
 * Term references are compared directly, unless one of them is null. Null is
 * a marker that this is a term constructor, in which case the comparison is
 * done by hand.
 */
bool term_ref_fat::operator == (const term_ref_fat& other) const {
  if (this->is_null()) {
    return cmp(other);
  }
  if (other.is_null()) {
    return other.cmp(*this);
  }
  return cmp(other);
}

void term_ref::to_stream(std::ostream& out) const {
  if (is_null()) {
    out << "null";
  } else {
    const term_manager_internal* tm = output::get_term_manager(out);
    if (tm == 0) {
      out << d_ref;
    } else {
      tm->term_of(*this).to_stream(out);
    }
  }
}

void term::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  const term_manager_internal* tm = output::get_term_manager(out);
  switch (lang) {
  case output::SMTLIB:
    to_stream_smt(out, *tm);
    break;
  default:
    assert(false);
  }
}

static inline
std::string get_smt_keyword(term_op op) {
  switch (op) {
  case TERM_EQ:
    return "=";
  case TERM_AND:
    return "and";
  case TERM_OR:
    return "or";
  case TERM_NOT:
    return "not";
  case TERM_IMPLIES:
    return "implies";
  case TERM_XOR:
    return "xor";
  case TERM_ADD:
    return "+";
  case TERM_SUB:
    return "-";
  case TERM_MUL:
    return "*";
  case TERM_DIV:
    return "/";
  case TERM_LEQ:
    return "<=";
  case TERM_LT:
    return "<";
  case TERM_GEQ:
    return ">=";
  case TERM_GT:
    return ">";
  case TERM_ITE:
    return "ite";
  case TYPE_BOOL:
    return "Bool";
  case TYPE_INTEGER:
    return "Integer";
  case TYPE_REAL:
    return "Real";
  default:
    assert(false);
    return "unknown";
  }
}

void term::to_stream_smt(std::ostream& out, const term_manager_internal& tm) const {
  switch (d_op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
    out << get_smt_keyword(d_op);
    break;
  case TYPE_STRUCT:
  {
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) { out << " "; }
      if (i % 2 == 0) { out << "("; }
      out << this->operator [](i);
      if (i % 2 == 1) { out << ")"; }
    }
    out << ")";
    break;
  }
  case VARIABLE:
    if (size() == 1) {
      out << tm.payload_of<std::string>(*this);
    } else {
      out << "[" << tm.payload_of<std::string>(*this) << ":";
      // The variables of the struct
      for (size_t i = 1; i < size(); ++ i) {
        out << " " << this->operator [](i);
      }
      out << "]";
    }
    break;
  case CONST_BOOL:
    out << (tm.payload_of<bool>(*this) ? "true" : "false");
    break;
  case TERM_EQ:
  case TERM_AND:
  case TERM_OR:
  case TERM_NOT:
  case TERM_IMPLIES:
  case TERM_XOR:
  case TERM_ITE:
  case TERM_ADD:
  case TERM_SUB:
  case TERM_MUL:
  case TERM_DIV:
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
  {
    if (size() > 0) {
      out << "(";
    }
    out << get_smt_keyword(d_op);
    for (const term_ref* it = begin(); it != end(); ++ it) {
      out << " " << *it;
    }
    if (size() > 0) {
      out << ")";
    }
    break;
  }
  case CONST_RATIONAL:
    // Stream is already in SMT mode
    out << tm.payload_of<rational>(*this);
    break;
  case CONST_STRING:
    out << tm.payload_of<std::string>(*this);
    break;
  default:
    assert(false);
  }
}

std::ostream& operator << (std::ostream& out, const set_tm& stm) {
  output::set_term_manager(out, stm.d_tm);
  return out;
}

term_ref_strong::term_ref_strong(const term_ref_strong& other)
: term_ref(other)
, d_tm(other.d_tm)
{
  if (d_tm != 0) {
    d_tm->attach(id());
  }
}

term_ref_strong::term_ref_strong(term_manager_internal& tm, term_ref ref)
: term_ref(ref)
, d_tm(&tm)
{
  d_tm->attach(id());
}

term_ref_strong::term_ref_strong(term_manager& tm, term_ref ref)
: term_ref(ref)
, d_tm(tm.get_internal())
{
  d_tm->attach(id());
}

term_ref_strong::~term_ref_strong() {
  if (d_tm != 0) {
    d_tm->detach(id());
  }
}

term_ref_strong& term_ref_strong::operator =(const term_ref_strong& other) {
  if (this != &other) {
    if (d_tm != 0) {
      d_tm->detach(id());
    }
    d_tm = other.d_tm;
    term_ref::operator=(other);
    if (d_tm != 0) {
      d_tm->attach(id());
    }
  }
  return *this;
}

size_t term_ref_strong::hash() const {
  if (d_tm == 0) {
    return 0;
  } else {
    return d_tm->hash_of(*this);
  }
}

size_t term_ref_strong::id() const {
  if (d_tm == 0) {
    return 0;
  } else {
    return d_tm->id_of(*this);
  }
}

/** Number of children, if any */
size_t term::size() const {
  return alloc::allocator<term, term_ref>::object_size(*this);
}

/** Returns the first child */
const term_ref* term::begin() const {
  return alloc::allocator<term, term_ref>::object_begin(*this);
}

/** The one past last child */
const term_ref* term::end() const {
  return alloc::allocator<term, term_ref>::object_end(*this);
}


}
}
