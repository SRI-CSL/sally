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
#include "utils/exception.h"

#include <iomanip>
#include <cassert>
#include <sstream>

namespace sally {
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
  case output::MCMT:
    to_stream_smt(out, *tm);
    break;
  case output::NUXMV:
    to_stream_nuxmv(out, *tm);
    break;
  case output::LUSTRE:
    to_stream_lustre(out, *tm);
    break;
  case output::HORN:
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

  case TERM_BV_ADD:
    return "bvadd";
  case TERM_BV_SUB:
    return "bvsub";
  case TERM_BV_MUL:
    return "bvmul";
  case TERM_BV_XOR:
    return "bvxor";
  case TERM_BV_SHL:
    return "bvshl";
  case TERM_BV_LSHR:
    return "bvlshr";
  case TERM_BV_ASHR:
    return "bvashr";
  case TERM_BV_NOT:
    return "bvnot";
  case TERM_BV_AND:
    return "bvand";
  case TERM_BV_OR:
    return "bvor";
  case TERM_BV_NAND:
    return "bvnand";
  case TERM_BV_NOR:
    return "bvnor";
  case TERM_BV_XNOR:
    return "bvxnor";
  case TERM_BV_CONCAT:
    return "concat";
  case TERM_BV_ULEQ:
    return "bvule";
  case TERM_BV_SLEQ:
    return "bvsle";
  case TERM_BV_ULT:
    return "bvult";
  case TERM_BV_SLT:
    return "bvslt";
  case TERM_BV_UGEQ:
    return "bvuge";
  case TERM_BV_SGEQ:
    return "bvsge";
  case TERM_BV_UGT:
    return "bvugt";
  case TERM_BV_SGT:
    return "bvsgt";
  case TERM_BV_UDIV:
    return "bvudiv";
  case TERM_BV_SDIV:
    return "bvsdiv";
  case TERM_BV_UREM:
    return "bvurem";
  case TERM_BV_SREM:
    return "bvsrem";
  case TERM_BV_SMOD:
    return "bvsmod";

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
  case TYPE_BITVECTOR: {
    size_t size = tm.payload_of<size_t>(*this);
    out << "(_ BitVec " << size << ")";
    break;
  }
  case VARIABLE: {
    std::string name = tm.payload_of<std::string>(*this);
    name = tm.name_normalize(name);
    if (size() == 1) {
      out << name;
    } else {
      out << "[" << name << ":";
      // The variables of the struct
      for (size_t i = 1; i < size(); ++ i) {
        out << " " << this->operator [](i);
      }
      out << "]";
    }
    break;
  }
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
  case TERM_BV_ADD:
  case TERM_BV_MUL:
  case TERM_BV_XOR:
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR:
  case TERM_BV_NOT:
  case TERM_BV_AND:
  case TERM_BV_OR:
  case TERM_BV_NAND:
  case TERM_BV_NOR:
  case TERM_BV_XNOR:
  case TERM_BV_CONCAT:
  case TERM_BV_ULEQ:
  case TERM_BV_SLEQ:
  case TERM_BV_ULT:
  case TERM_BV_SLT:
  case TERM_BV_UGEQ:
  case TERM_BV_SGEQ:
  case TERM_BV_UGT:
  case TERM_BV_SGT:
  case TERM_BV_UDIV:
  case TERM_BV_SDIV:
  case TERM_BV_UREM:
  case TERM_BV_SREM:
  case TERM_BV_SMOD:
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
  case TERM_BV_SUB:
  {
    out << "(";
    if (size() == 1) {
      out << "bvneg" << " " << (*this)[0];
    } else {
      assert(size() == 2);
      out << "bvsub" << " " << (*this)[0] << " " << (*this)[1];
    }
    out << ")";
    break;
  }
  case TERM_BV_EXTRACT: {
    const bitvector_extract& extract = tm.payload_of<bitvector_extract>(*this);
    out << "((_ extract " << extract.high << " " << extract.low << ") " << *begin() << ")";
    break;
  }
  case CONST_RATIONAL:
    // Stream is already in SMT mode
    out << tm.payload_of<rational>(*this);
    break;
  case CONST_INTEGER:
    // Stream is already in SMT mode
    out << tm.payload_of<integer>(*this);
    break;
  case CONST_BITVECTOR:
    out << tm.payload_of<bitvector>(*this);
    break;
  case CONST_STRING:
    out << tm.payload_of<std::string>(*this);
    break;
  default:
    assert(false);
  }
}

inline
std::string get_nuxmv_operator(expr::term_op op) {
  switch (op) {
  case TERM_AND: return "&";
  case TERM_OR: return "|";
  case TERM_ADD: return "+";
  case TERM_XOR: return "xor";
  case TERM_MUL: return "*";
  case TERM_BV_ADD: return "+";
  case TERM_BV_MUL: return "*";
  case TERM_BV_XOR: return "xor";
  case TERM_BV_AND: return "&";
  case TERM_BV_OR: return "|";
  case TERM_BV_CONCAT: return "::";
  default:
    assert(false);
  }
  return "unknown";
}

void term::to_stream_nuxmv(std::ostream& out, const term_manager_internal& tm) const {
  switch (d_op) {
  case TYPE_BOOL:
    out << "boolean";
    break;
  case TYPE_INTEGER:
    out << "integer";
    break;
  case TYPE_REAL:
    out << "real";
    break;
  case TYPE_BITVECTOR: {
    size_t size = tm.payload_of<size_t>(*this);
    out << "unsigned word[" << size << "]";
    break;
  }
  case VARIABLE: {
    std::string name = tm.payload_of<std::string>(*this);
    name = tm.name_normalize(name);
    if (size() == 1) {
      out << name;
    } else {
      out << "[" << name << ":";
      // The variables of the struct
      for (size_t i = 1; i < size(); ++ i) {
        out << " " << this->operator [](i);
      }
      out << "]";
    }
    break;
  }
  case CONST_BOOL:
    out << (tm.payload_of<bool>(*this) ? "TRUE" : "FALSE");
    break;
  case TERM_EQ:
    out << "(" << child(0) << " = " << child(1) << ")";
    break;
  case TERM_IMPLIES:
    out << "(" << child(0) << " -> " << child(1) << ")";
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_ADD:
  case TERM_XOR:
  case TERM_MUL:
  case TERM_BV_ADD:
  case TERM_BV_MUL:
  case TERM_BV_XOR:
  case TERM_BV_AND:
  case TERM_BV_OR:
  case TERM_BV_CONCAT:
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) out << " " << get_nuxmv_operator(d_op) << " ";
      out << child(i);
    }
    out << ")";
    break;
  case TERM_NOT:
    out << "(!" << child(0) << ")";
    break;
  case TERM_ITE:
    out << "(" << child(0) << " ? " << child(1) << " : " << child(2) << ")";
    break;
  case TERM_SUB:
    if (size() == 1) {
      out << "(- " << child(0) << ")";
    } else {
      out << "(" << child(0) << " - " << child(1) << ")";
    }
    break;
  case TERM_DIV: {
    term_ref c1 = child(0);
    term_ref c2 = child(1);
    const term& c2_term = tm.term_of(c2);
    expr::rational r;
    if (c2_term.op() == CONST_RATIONAL) {
      r = tm.payload_of<rational>(c2_term).invert();
    } else if (c2_term.op() == CONST_INTEGER) {
      r = tm.payload_of<integer>(c2_term);
      r = r.invert();
    } else {
      throw exception("Division by non-constants is not supported!");
    }
    out << "(" << c1 << " * " << r << ")";
    break;
  }
  case TERM_LEQ:
    out << "(" << child(0) << " <= " << child(1) << ")";
    break;
  case TERM_LT:
    out << "(" << child(0) << " < " << child(1) << ")";
    break;
  case TERM_GEQ:
    out << "(" << child(0) << " >= " << child(1) << ")";
    break;
  case TERM_GT:
    out << "(" << child(0) << " > " << child(1) << ")";
    break;
  case TERM_BV_SUB:
    out << "(" << child(0) << " - " << child(1) << ")";
    break;
  case TERM_BV_SHL:
    out << "(" << child(0) << " << " << child(1) << ")";
    break;
  case TERM_BV_LSHR:
    out << "(" << child(0) << " >> " << child(1) << ")";
    break;
  case TERM_BV_ASHR:
    out << "unsigned(signed(" << child(0) << ") << " << child(1) << ")";
    break;
  case TERM_BV_NOT:
    out << "(!" << child(0) << ")";
    break;
  case TERM_BV_NAND:
    out << "(!(" << child(0) << " & " << child(1) << "))";
    break;
  case TERM_BV_NOR:
    out << "(!(" << child(0) << " | " << child(1) << "))";
    break;
  case TERM_BV_XNOR:
    out << "(" << child(0) << " xnor " << child(1) << ")";
    break;
  case TERM_BV_ULEQ:
    out << "(" << child(0) << " <= " << child(1) << ")";
    break;
  case TERM_BV_SLEQ:
    out << "(signed(" << child(0) << ") <= signed(" << child(1) << "))";
    break;
  case TERM_BV_ULT:
    out << "(" << child(0) << " < " << child(1) << ")";
    break;
  case TERM_BV_SLT:
    out << "(signed(" << child(0) << ") < signed(" << child(1) << "))";
    break;
  case TERM_BV_UGEQ:
    out << "(" << child(0) << " >= " << child(1) << ")";
    break;
  case TERM_BV_SGEQ:
    out << "(signed(" << child(0) << ") >= signed(" << child(1) << "))";
    break;
  case TERM_BV_UGT:
    out << "(" << child(0) << " > " << child(1) << ")";
    break;
  case TERM_BV_SGT:
    out << "(signed(" << child(0) << ") > signed(" << child(1) << "))";
    break;
  case TERM_BV_UDIV:
    out << "(" << child(0) << " / " << child(1) << ")";
    break;
  case TERM_BV_SDIV:
    out << "(signed(" << child(0) << ") / signed(" << child(1) << "))";
    break;
  case TERM_BV_UREM: // MOD
    out << "(" << child(0) << " mod " << child(1) << ")";
    break;
  case TERM_BV_SREM: // MOD
    out << "(signed(" << child(0) << ") mod signed(" << child(1) << "))";
    break;
  case TERM_BV_SMOD:
    throw exception("SMOD not yet supported!");
    break;
  case TERM_BV_EXTRACT: {
    const bitvector_extract& extract = tm.payload_of<bitvector_extract>(*this);
    out << child(0) << "[" << extract.high << ":" << extract.low << "]";
    break;
  }
  case CONST_RATIONAL:
    // Stream is already in NUXMV mode
    out << tm.payload_of<rational>(*this);
    break;
  case CONST_INTEGER:
    // Stream is already in NUXMV mode
    out << tm.payload_of<integer>(*this);
    break;
  case CONST_BITVECTOR:
    // Stream is already in NUXMV mode
    out << tm.payload_of<bitvector>(*this);
    break;
  case CONST_STRING:
    out << tm.payload_of<std::string>(*this);
    break;
  default:
    assert(false);
  }
}

inline
std::string get_lustre_operator(expr::term_op op) {
  switch (op) {
  case TERM_AND: return "and";
  case TERM_OR: return "or";
  case TERM_ADD: return "+";
  case TERM_XOR: return "xor";
  case TERM_MUL: return "*";
  default:
    return "??";
  }
}

void term::to_stream_lustre(std::ostream& out, const term_manager_internal& tm) const {
  bool unsupported = false;

  switch (d_op) {
  case TYPE_BOOL:
    out << "bool";
    break;
  case TYPE_INTEGER:
    out << "integer";
    break;
  case TYPE_REAL:
    out << "real";
    break;
  case VARIABLE: {
    std::string name = tm.payload_of<std::string>(*this);
    name = tm.name_normalize(name);
    if (size() == 1) {
      out << name;
    } else {
      unsupported = true;
    }
    break;
  }
  case CONST_BOOL:
    out << (tm.payload_of<bool>(*this) ? "true" : "false");
    break;
  case CONST_RATIONAL:
    out << tm.payload_of<rational>(*this);
    break;
  case CONST_INTEGER:
    out << tm.payload_of<integer>(*this);
    break;
  case TERM_EQ:
    out << "(" << child(0) << " = " << child(1) << ")";
    break;
  case TERM_IMPLIES:
    out << "(not " << child(0) << " or " << child(1) << ")";
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_ADD:
  case TERM_XOR:
  case TERM_MUL:
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) out << " " << get_lustre_operator(d_op) << " ";
      out << child(i);
    }
    out << ")";
    break;
  case TERM_NOT:
    out << "(not " << child(0) << ")";
    break;
  case TERM_ITE:
    out << "(if " << child(0) << " then " << child(1) << " else " << child(2) << ")";
    break;
  case TERM_SUB:
    if (size() == 1) {
      out << "(- " << child(0) << ")";
    } else {
      out << "(" << child(0) << " - " << child(1) << ")";
    }
    break;
  case TERM_DIV:
    out << "(" << child(0) << "/" << child(1) << ")";
    break;
  case TERM_LEQ:
    out << "(" << child(0) << " <= " << child(1) << ")";
    break;
  case TERM_LT:
    out << "(" << child(0) << " < " << child(1) << ")";
    break;
  case TERM_GEQ:
    out << "(" << child(0) << " >= " << child(1) << ")";
    break;
  case TERM_GT:
    out << "(" << child(0) << " > " << child(1) << ")";
    break;
  default:
    unsupported = true;
    break;
  }

  if (unsupported) {
    std::stringstream ss;
    ss << "Output for " << d_op << " not supported in Lustre.";
    throw exception(ss.str());
  }
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
