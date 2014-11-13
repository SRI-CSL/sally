/*
 * term.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include "expr/term.h"
#include "utils/output.h"

#include <iomanip>
#include <cassert>

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

term_manager::term_manager(bool typecheck)
: d_typecheck(typecheck)
{
  // The null id
  new_term_id();

  // Initialize all payload memories to 0
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    d_payload_memory[i] = 0;
  }

  // Create the types
  d_booleanType = mk_term<TYPE_BOOL>(alloc::empty_type());
  d_integerType = mk_term<TYPE_INTEGER>(alloc::empty_type());
  d_realType = mk_term<TYPE_REAL>(alloc::empty_type());
}

void term_ref::to_stream(std::ostream& out) const {
  if (is_null()) {
    out << "null";
  } else {
    const term_manager* tm = output::get_term_manager(out);
    if (tm == 0) {
      out << d_ref;
    } else {
      tm->term_of(*this).to_stream(out);
    }
  }
}

void term::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  const term_manager* tm = output::get_term_manager(out);
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

void term::to_stream_smt(std::ostream& out, const term_manager& tm) const {
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
      if (i%2) { out << " "; }
      else { out << " ("; }
      out << this->operator [](i);
      if (i%2) { out << ")"; }
    }
    out << ")";
    break;
  }
  case VARIABLE:
    out << tm.payload_of<std::string>(*this);
    break;
  case CONST_BOOL:
    out << (tm.payload_of<bool>(*this) ? "true" : "false");
    break;
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

term_manager::~term_manager() {
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    delete d_payload_memory[i];
  }
}

std::ostream& operator << (std::ostream& out, const set_tm& stm) {
  output::set_term_manager(out, stm.tm);
  return out;
}

bool is_type(term_op op) {
  switch (op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
    return true;
  default:
    return false;
  }
}

term_ref term_manager::type_of(const term& t) const {
  switch (t.op()) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
    return term_ref();
  case VARIABLE:
    return t[0];
  // Equality
  case TERM_EQ:
    return booleanType();
    break;
  // ITE
  case TERM_ITE:
    return type_of(t[1]);
  // Boolean terms
  case CONST_BOOL:
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
  case TERM_NOT:
  case TERM_IMPLIES:
    return booleanType();
  // Arithmetic terms
  case CONST_RATIONAL:
  case TERM_ADD:
  case TERM_MUL:
  case TERM_SUB:
  case TERM_DIV:
    return d_realType;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    return d_booleanType;
  case CONST_STRING:
    return term_ref();
  default:
    assert(false);
  }
  return term_ref();
}

term_ref_strong::term_ref_strong(const term_ref_strong& other)
: term_ref(other)
, d_tm(other.d_tm)
{
  if (d_tm != 0) {
    d_tm->attach(id());
  }
}

term_ref_strong::term_ref_strong(term_manager& tm, term_ref ref)
: term_ref(ref)
, d_tm(&tm)
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

term_ref term_manager::tcc_of(const term& t) const {
  tcc_map::const_iterator find = d_tcc_map.find(ref_of(t));
  if (find == d_tcc_map.end()) {
    return term_ref();
  } else {
    return find->second;
  }
}

bool term_manager::typecheck(term_ref t_ref) {
  const term& t = term_of(t_ref);
  term_op op = t.op();

  bool ok = true;

  switch (op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case VARIABLE:
    break;
  case TYPE_STRUCT: {
    for (size_t i = 0; ok && i < t.size(); ++ i) {
      if (i%2) {
        ok = term_of(t[i]).op() == CONST_STRING;
      } else {
        ok = is_type(term_of(t[i]).op());
      }
    }
    break;
  }
  // Equality
  case TERM_EQ:
    ok = (t.size() == 2 && type_of(t[0]) == type_of(t[1]));
    break;
  // ITE
  case TERM_ITE:
    ok = (t.size() == 3 && type_of(t[0]) == booleanType() &&
        type_of(t[1]) == type_of(t[2]));
    break;
  // Boolean terms
  case CONST_BOOL:
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
    if (t.size() < 2) {
      ok = false;
    } else {
      for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
        if (type_of(*it) != booleanType()) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_NOT:
    if (t.size() != 1) {
      ok = false;
    } else {
      ok = type_of(t[0]) == booleanType();
    }
    break;
  case TERM_IMPLIES:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == booleanType() && type_of(t[1]) == booleanType();
    }
    break;
  // Arithmetic terms
  case CONST_RATIONAL:
    break;
  case TERM_ADD:
  case TERM_MUL:
    if (t.size() < 2) {
      ok = false;
    } else {
      for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
        if (type_of(*it) != realType()) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_SUB:
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
    }
    break;
  case TERM_DIV:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
      // TODO: make TCC
    }
    break;
  case CONST_STRING:
    ok = true;
    break;
  default:
    assert(false);
  }

  return ok;
}

void term_manager::to_stream(std::ostream& out) const {
  out << "Term memory:" << std::endl;
  out << d_memory << std::endl;

  for (int op = 0; op < OP_LAST; ++ op) {
    out << "Payloads of :" << (term_op) op << std::endl;
    if (d_payload_memory[op]) {
      out << *d_payload_memory[op] << std::endl;
    } else {
      out << "null" << std::endl;
    }
  }

  out << "Terms:" << std::endl;
  for (term_ref_hash_set::const_iterator it = d_pool.begin(); it != d_pool.end(); ++ it) {
    out << "[id: " << it->id() << ", ref_count = " << d_term_refcount[it->id()] << "] : " << *it << std::endl;
  }
}

term_ref term_manager::mk_term(term_op op, const std::vector<term_ref>& children) {

  term_ref result;

#define SWITCH_TO_TERM(OP) case OP: result = mk_term<OP>(children.begin(), children.end()); break;

  switch (op) {
    SWITCH_TO_TERM(TYPE_BOOL)
    SWITCH_TO_TERM(TYPE_INTEGER)
    SWITCH_TO_TERM(TYPE_REAL)
    SWITCH_TO_TERM(TERM_EQ)
    SWITCH_TO_TERM(TERM_ITE)
    SWITCH_TO_TERM(TERM_AND)
    SWITCH_TO_TERM(TERM_OR)
    SWITCH_TO_TERM(TERM_NOT)
    SWITCH_TO_TERM(TERM_IMPLIES)
    SWITCH_TO_TERM(TERM_XOR)
    SWITCH_TO_TERM(TERM_ADD)
    SWITCH_TO_TERM(TERM_SUB)
    SWITCH_TO_TERM(TERM_MUL)
    SWITCH_TO_TERM(TERM_DIV)
    SWITCH_TO_TERM(TERM_LEQ)
    SWITCH_TO_TERM(TERM_LT)
    SWITCH_TO_TERM(TERM_GEQ)
    SWITCH_TO_TERM(TERM_GT)
  default:
    assert(false);
  }

#undef SWITCH_TO_TERM

  return result;
}

}
}
