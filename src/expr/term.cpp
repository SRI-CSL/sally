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

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/term_manager_internal.h"
#include "utils/allocator.h"
#include "utils/output.h"
#include "utils/exception.h"
#include "utils/string.h"

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
    const term_manager* tm = output::get_term_manager(out);
    if (tm == 0) {
      out << d_ref;
    } else {
      tm->term_of(*this).to_stream(out);
    }
  }
}

void term::mk_let_cache(term_manager& tm, expr_let_cache& let_cache, std::vector<expr::term_ref>& definitions) const {

  expr::term_ref ref = tm.ref_of(*this);
  expr_let_cache::const_iterator find = let_cache.find(ref);
  if (find != let_cache.end()) {
    return;
  }

  bool record_let = true;

  // Whether to record the let, and work on the children
  switch(d_op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
  case TYPE_BITVECTOR:
  case TYPE_STRING:
  case TYPE_TYPE:
  case VARIABLE:
  case TERM_FUN_APP:
  case CONST_BOOL:
  case CONST_RATIONAL:
  case CONST_BITVECTOR:
  case CONST_STRING:
    record_let = false;
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
  case TERM_MOD:
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
  case TERM_TO_INT:
  case TERM_TO_REAL:
  case TERM_IS_INT:
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
  case TERM_BV_SUB:
  case TERM_BV_EXTRACT:
  case TERM_BV_SGN_EXTEND:
    for (const term_ref* it = begin(); it != end(); ++ it) {
      const term& child = tm.term_of(*it);
      child.mk_let_cache(tm, let_cache, definitions);
    }
    break;
  default:
    assert(false);
  }

  // Record the mapping
  if (record_let) {
    std::string name = tm.get_fresh_variable_name();
    let_cache[ref] = name;
    definitions.push_back(ref);
  }

}

void term::to_stream(std::ostream& out) const {
  // Get the output language
  output::language lang = output::get_output_language(out);

  // Get the term manager
  term_manager* tm = output::get_term_manager(out);
  if (tm == 0) {
    throw exception("No expression manager set for the output stream");
  }

  expr_let_cache let_cache;

  // Print
  switch (lang) {
  case output::MCMT:
  case output::HORN: {
    if (output::get_use_lets(out)) {
      std::vector<expr::term_ref> definitions;
      mk_let_cache(*tm, let_cache, definitions);
      to_stream_smt_with_let(out, *tm, let_cache, definitions);
      tm->reset_fresh_variables();
    } else {
      to_stream_smt_without_let(out, *tm, let_cache, false);
    }
    break;
  }
  case output::NUXMV:
    to_stream_nuxmv_without_let(out, *tm, let_cache);
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
    return "=>";
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
  case TERM_MOD:
    return "%";
  case TERM_LEQ:
    return "<=";
  case TERM_LT:
    return "<";
  case TERM_GEQ:
    return ">=";
  case TERM_GT:
    return ">";
  case TERM_TO_INT:
    return "to_int";
  case TERM_TO_REAL:
    return "to_real";
  case TERM_IS_INT:
    return "is_int";
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

  case TERM_ARRAY_READ:
    return "select";
  case TERM_ARRAY_WRITE:
    return "store";

  case TYPE_BOOL:
    return "Bool";
  case TYPE_INTEGER:
    return "Int";
  case TYPE_REAL:
    return "Real";
  case TYPE_STRING:
    return "String";
  case TYPE_TYPE:
    return "Type";

  default:
    assert(false);
    return "unknown";
  }
}

void term::to_stream_smt_with_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, const std::vector<expr::term_ref>& definitions) const {

  assert(let_cache.size() == definitions.size());

  // (let ...
  for (size_t i = 0; i < definitions.size(); ++ i) {
    out << "(let (";
    expr_let_cache::const_iterator find = let_cache.find(definitions[i]);
    assert(find != let_cache.end());
    out << "(" << find->second << " ";
    const term& t = tm.term_of(find->first);
    t.to_stream_smt_without_let(out, tm, let_cache, false);
    out << ")) ";
  }
  // t
  to_stream_smt_without_let(out, tm, let_cache);
  // close the lets
  for (size_t i = 0; i < definitions.size(); ++ i) {
    out << ")";
  }
}

#define SMT_REF_OUT(ref) tm.term_of(ref).to_stream_smt_without_let(out, tm, let_cache);

static inline
bool isalnum_not(char c) { return !isalnum(c); }

void term::to_stream_smt_without_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, bool use_cache) const {

  // The internals
  const term_manager_internal& tm_internal = *tm.get_internal();

  // See if it's been cached already
  if (use_cache) {
    expr_let_cache::const_iterator find = let_cache.find(tm_internal.ref_of(*this));
    if (find != let_cache.end()) {
      out << find->second;
      return;
    }
  }

  switch (d_op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRING:
  case TYPE_TYPE:
    out << get_smt_keyword(d_op);
    break;
  case TYPE_STRUCT:
  {
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) { out << " "; }
      if (i % 2 == 0) { out << "("; }
      SMT_REF_OUT(child(i));
      if (i % 2 == 1) { out << ")"; }
    }
    out << ")";
    break;
  }
  case TYPE_ARRAY:
  {
    out << "(Array";
    for (size_t i = 0; i < size(); ++ i) {
      out << " ";
      SMT_REF_OUT(child(i));
    }
    out << ")";
    break;
    break;
  }
  case TYPE_TUPLE:
  {
    out << "(tuple";
    for (size_t i = 0; i < size(); ++ i) {
      out << " ";
      SMT_REF_OUT(child(i));
    }
    out << ")";
    break;
  }
  case TYPE_RECORD:
  {
    out << "(record";
    for (size_t i = 0; i < size(); i += 2) {
      out << " (";
      SMT_REF_OUT(child(i))
      out << " ";
      SMT_REF_OUT(child(i+1));
      out << ")";
    }
    out << ")";
    break;
  }
  case TYPE_ENUM:
  {
    out << "(enum";
    for (size_t i = 0; i < size(); ++ i) {
      out << " ";
      SMT_REF_OUT(child(i));
    }
    out << ")";
    break;
  }
  case TYPE_FUNCTION:
  {
    out << "(";
    for (size_t i = 0; i+1 < size(); ++ i) {
      if (i) { out << " "; }
      SMT_REF_OUT(child(i));
    }
    out << ") ";
    SMT_REF_OUT(child(size()-1));
    break;
  }
  case TYPE_BITVECTOR: {
    size_t size = tm_internal.payload_of<size_t>(*this);
    out << "(_ BitVec " << size << ")";
    break;
  }
  case VARIABLE: {
    std::string name(tm_internal.payload_of<utils::string>(*this).c_str());
    name = tm_internal.name_normalize(name);
    // Escape if needed
    if (find_if(name.begin(), name.end(), isalnum_not) != name.end()) {
      name = "|" + name + "|";
    }
    if (size() == 1) {
      out << name;
    } else {
      out << "[" << name << ":";
      // The variables of the struct
      for (size_t i = 1; i < size(); ++ i) {
        out << " ";
        SMT_REF_OUT(child(i));
      }
      out << "]";
    }
    break;
  }
  case CONST_BOOL:
    out << (tm_internal.payload_of<bool>(*this) ? "true" : "false");
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
  case TERM_MOD:
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
  case TERM_TO_INT:
  case TERM_TO_REAL:
  case TERM_IS_INT:
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
  case TERM_ARRAY_READ:
  case TERM_ARRAY_WRITE:
  {
    if (size() > 0) {
      out << "(";
    }
    out << get_smt_keyword(d_op);
    for (const term_ref* it = begin(); it != end(); ++ it) {
      out << " ";
      SMT_REF_OUT(*it);
    }
    if (size() > 0) {
      out << ")";
    }
    break;
  }
  case TERM_BV_ADD:
  case TERM_BV_CONCAT:
  {
    // Some solver (looking at you MathSAT), don't take non-binary concats
    // so we print (concat (concat a b) c)
    for (size_t i = 1; i < size(); ++ i) {
      out << "(" << get_smt_keyword(d_op) << " ";
    }
    const term_ref* it = begin();
    out << *it;
    for (++ it; it != end(); ++ it) {
      out << " ";
      SMT_REF_OUT(*it);
      out << ")";
    }
    break;
  }
  case TERM_BV_SUB:
  {
    out << "(";
    if (size() == 1) {
      out << "bvneg" << " ";
      SMT_REF_OUT(child(0));
    } else {
      assert(size() == 2);
      out << "bvsub" << " ";
      SMT_REF_OUT(child(0));
      out << " ";
      SMT_REF_OUT(child(1));
    }
    out << ")";
    break;
  }
  case TERM_BV_EXTRACT: {
    const bitvector_extract& extract = tm_internal.payload_of<bitvector_extract>(*this);
    out << "((_ extract " << extract.high << " " << extract.low << ") ";
    SMT_REF_OUT(child(0));
    out << ")";
    break;
  }
  case TERM_BV_SGN_EXTEND: {
    const bitvector_sgn_extend& extend = tm_internal.payload_of<bitvector_sgn_extend>(*this);
    out << "((_ sign_extend " << extend.size << ") ";
    SMT_REF_OUT(child(0));
    out << ")";
    break;
  }
  case TERM_TUPLE_CONSTRUCT: {
    out << "(mk-tuple";
    for (size_t i = 0; i < size(); ++ i) {
      out << " ";
      SMT_REF_OUT(child(i));
    }
    out << ")";
    break;
  }
  case TERM_TUPLE_READ: {
    out << "(tuple-read ";
    SMT_REF_OUT(child(0));
    out << " " << tm_internal.payload_of<size_t>(*this) << ")";
    break;
  }
  case TERM_TUPLE_WRITE: {
    out << "(tuple-write ";
    SMT_REF_OUT(child(0));
    out << " " << tm_internal.payload_of<size_t>(*this) << " ";
    SMT_REF_OUT(child(1));
    out << ")";
    break;
  }
  case TERM_RECORD_CONSTRUCT: {
    out << "(mk-record";
    for (size_t i = 0; i < size(); i += 2) {
      out << " (";
      SMT_REF_OUT(child(i));
      out << " ";
      SMT_REF_OUT(child(i+1));
      out << ")";
    }
    out << ")";
    break;
  }
  case TERM_RECORD_READ: {
    out << "(record-read ";
    SMT_REF_OUT(child(0));
    out << " ";
    SMT_REF_OUT(child(1));
    out << ")";
    break;
  }
  case TERM_RECORD_WRITE: {
    out << "(record-write ";
    SMT_REF_OUT(child(0));
    out << " ";
    SMT_REF_OUT(child(1));
    out << " ";
    SMT_REF_OUT(child(2));
    out << ")";
    break;
  }
  case TERM_FUN_APP: {
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) { out << " "; }
      SMT_REF_OUT(child(i));
    }
    out << ")";
    break;
  }
  case TERM_LAMBDA:
  case TERM_EXISTS:
  case TERM_FORALL:
  case TYPE_PREDICATE_SUBTYPE:
  case TERM_ARRAY_LAMBDA:
  {
    if (d_op == TERM_LAMBDA) { out << "(lambda ("; }
    if (d_op == TERM_EXISTS) { out << "(exists ("; }
    if (d_op == TERM_FORALL) { out << "(forall ("; }
    if (d_op == TYPE_PREDICATE_SUBTYPE) { out << "(subtype ("; }
    if (d_op == TERM_ARRAY_LAMBDA) { out << "(array ("; }
    for (size_t i = 0; i + 1 < size(); ++ i) {
      if (i) { out << " "; }
      out << "(";
      term_ref a = child(i);
      term_ref a_type = tm_internal.type_of_if_exists(a);
      SMT_REF_OUT(a);
      out << " ";
      SMT_REF_OUT(a_type);
      out << ")";
    }
    out << ") ";
    SMT_REF_OUT(child(size()-1));
    out << ")";
    break;
  }
  case CONST_RATIONAL:
    // Stream is already in SMT mode
    out << tm_internal.payload_of<rational>(*this);
    break;
  case CONST_BITVECTOR:
    out << tm_internal.payload_of<bitvector>(*this);
    break;
  case CONST_STRING:
    out << tm_internal.payload_of<utils::string>(*this);
    break;
  case CONST_ENUM: {
    size_t id = tm_internal.payload_of<size_t>(*this);
    const term& enum_type = tm_internal.term_of(child(0));
    out << enum_type[id];
    break;
  }
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

  case TERM_LEQ: return "<=";
  case TERM_LT: return "<";
  case TERM_GEQ: return ">=";
  case TERM_GT: return ">";
  case TERM_BV_SUB: return "-";
  case TERM_BV_SHL: return "<<";
  case TERM_BV_LSHR: return ">>";

  case TERM_BV_XNOR: return "xnor";
  case TERM_BV_ULEQ: return "<=";
  case TERM_BV_ULT: return "<";
  case TERM_BV_UGEQ: return ">=";
  case TERM_BV_UGT: return ">";
  case TERM_BV_UDIV: return "/";
  case TERM_BV_UREM: return "mod";
  default:
    assert(false);
  }
  return "unknown";
}

#define SMV_REF_OUT(ref) tm.term_of(ref).to_stream_nuxmv_without_let(out, tm, let_cache);

void term::to_stream_nuxmv_without_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, bool use_cache_for_root) const {

  // The internals
  const term_manager_internal& tm_internal = *tm.get_internal();

  // See if it's been cached already
  if (use_cache_for_root) {
    expr_let_cache::const_iterator find = let_cache.find(tm_internal.ref_of(*this));
    if (find != let_cache.end()) {
      out << find->second;
      return;
    }
  }

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
    size_t size = tm_internal.payload_of<size_t>(*this);
    out << "unsigned word[" << size << "]";
    break;
  }
  case VARIABLE: {
    std::string name(tm_internal.payload_of<utils::string>(*this).c_str());
    name = tm_internal.name_normalize(name);
    if (size() == 1) {
      out << name;
    } else {
      out << "[" << name << ":";
      // The variables of the struct
      for (size_t i = 1; i < size(); ++ i) {
        out << " ";
        SMV_REF_OUT(child(i));
      }
      out << "]";
    }
    break;
  }
  case CONST_BOOL:
    out << (tm_internal.payload_of<bool>(*this) ? "TRUE" : "FALSE");
    break;
  case TERM_EQ:
    out << "(";
    SMV_REF_OUT(child(0));
    out << " = ";
    SMV_REF_OUT(child(1));
    out << ")";
    break;
  case TERM_IMPLIES:
    out << "(";
    SMV_REF_OUT(child(0));
    out << " -> ";
    SMV_REF_OUT(child(1));
    out << ")";
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_ADD:
  case TERM_XOR:
  case TERM_MUL:
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
  case TERM_BV_ADD:
  case TERM_BV_MUL:
  case TERM_BV_XOR:
  case TERM_BV_AND:
  case TERM_BV_OR:
  case TERM_BV_CONCAT:
  case TERM_BV_SUB:
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_XNOR:
  case TERM_BV_ULEQ:
  case TERM_BV_ULT:
  case TERM_BV_UGEQ:
  case TERM_BV_UGT:
  case TERM_BV_UDIV:
  case TERM_BV_UREM:
    out << "(";
    for (size_t i = 0; i < size(); ++ i) {
      if (i) out << " " << get_nuxmv_operator(d_op) << " ";
      SMV_REF_OUT(child(i));
    }
    out << ")";
    break;
  case TERM_NOT:
    out << "(!";
    SMV_REF_OUT(child(0));
    out << ")";
    break;
  case TERM_ITE:
    out << "(";
    SMV_REF_OUT(child(0));
    out << " ? ";
    SMV_REF_OUT(child(1));
    out << " : ";
    SMV_REF_OUT(child(2));
    out << ")";
    break;
  case TERM_SUB:
    if (size() == 1) {
      out << "(- " << child(0) << ")";
    } else {
      out << "(";
      SMV_REF_OUT(child(0));
      out << " - ";
      SMV_REF_OUT(child(1));
      out << ")";
    }
    break;
  case TERM_DIV: {
    term_ref c1 = child(0);
    term_ref c2 = child(1);
    const term& c2_term = tm_internal.term_of(c2);
    expr::rational r;
    if (c2_term.op() == CONST_RATIONAL) {
      r = tm_internal.payload_of<rational>(c2_term).invert();
    } else {
      throw exception("Division by non-constants is not supported!");
    }
    out << "(";
    SMV_REF_OUT(c1);
    out << " * " << r << ")";
    break;
  }
  case TERM_BV_ASHR:
    out << "unsigned(signed(";
    SMV_REF_OUT(child(0));
    out << ") << ";
    SMV_REF_OUT(child(1));
    out << ")";
    break;
  case TERM_BV_NOT:
    out << "(!";
    SMV_REF_OUT(child(0));
    out << ")";
    break;
  case TERM_BV_NAND:
    out << "(!(";
    SMV_REF_OUT(child(0));
    out << " & ";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_NOR:
    out << "(!(" << child(0) << " | ";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SLEQ:
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") <= signed(";
    SMV_REF_OUT(child(1));
    out << "))";
    break;
  case TERM_BV_SLT:
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") < signed(";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SGEQ:
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") >= signed(";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SGT:
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") > signed(";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SDIV:
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") / signed(";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SREM: // MOD
    out << "(signed(";
    SMV_REF_OUT(child(0));
    out << ") mod signed(";
    SMV_REF_OUT(child(1));
    out <<"))";
    break;
  case TERM_BV_SMOD:
    throw exception("SMOD not yet supported!");
    break;
  case TERM_BV_EXTRACT: {
    const bitvector_extract& extract = tm_internal.payload_of<bitvector_extract>(*this);
    out << child(0) << "[" << extract.high << ":" << extract.low << "]";
    break;
  }
  case TERM_BV_SGN_EXTEND: {
    const bitvector_sgn_extend& extend = tm_internal.payload_of<bitvector_sgn_extend>(*this);
    out << "(" << child(0) << " sgn_extend " << extend.size << ")";
    break;
  }
  case CONST_RATIONAL:
    // Stream is already in NUXMV mode
    out << tm_internal.payload_of<rational>(*this);
    break;
  case CONST_BITVECTOR:
    // Stream is already in NUXMV mode
    out << tm_internal.payload_of<bitvector>(*this);
    break;
  case CONST_STRING:
    out << tm_internal.payload_of<utils::string>(*this);
    break;
  default:
    assert(false);
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
