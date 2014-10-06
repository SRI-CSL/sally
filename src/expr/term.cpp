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
namespace term {

term_manager::term_manager() {
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    d_payload_memory[i] = 0;
  }
}

void term_manager::term_ref::to_stream(std::ostream& out) const {
  const term_manager* tm = output::get_term_manager(out);
  if (tm == 0) {
    out << d_ref;
  } else {
    tm->term_of(*this).to_stream(out);
  }
}

void term_manager::term::to_stream(std::ostream& out) const {
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
  case OP_AND:
    return "and";
  case OP_OR:
    return "or";
  case OP_NOT:
    return "not";
  case OP_IMPLIES:
    return "implies";
  case OP_XOR:
    return "xor";
  case OP_ADD:
    return "+";
  case OP_SUB:
    return "-";
  case OP_MUL:
    return "*";
  case OP_DIV:
    return "/";
  default:
    assert(false);
    return "unknown";
  }
}

void term_manager::term::to_stream_smt(std::ostream& out, const term_manager& tm) const {
  switch (d_op) {
  case OP_VARIABLE:
    out << "var";
    break;
  case OP_BOOL_CONSTANT:
    out << (tm.payload_of<bool>(*this) ? "true" : "false");
    break;
  case OP_AND:
  case OP_OR:
  case OP_NOT:
  case OP_IMPLIES:
  case OP_XOR:
  case OP_ADD:
  case OP_SUB:
  case OP_MUL:
  case OP_DIV: {
    out << "(" << get_smt_keyword(d_op);
    for (const term_ref* it = tm.term_begin(*this); it != tm.term_end(*this); ++ it) {
      out << " " << *it;
    }
    out << ")";
    break;
  }
  case OP_REAL_CONSTANT:
    // Stream is already in SMT mode
    out << tm.payload_of<rational>(*this);
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

int term_manager::cmp(const term& t1, const term& t2) const {

  // Compare the ops
  int op_cmp = t1.d_op - t2.d_op;
  if (op_cmp != 0) return op_cmp;

  // Compare the payload references, if any
  int payload_cmp = t1.d_payload.cmp(t2.d_payload);
  if (payload_cmp != 0) {
    // References are the same, but the payloads themselves might be different
  }

  // Compare the sizes
  int size_cmp = (int)term_size(t1) - (int)term_size(t2);
  if (size_cmp != 0) {
    return size_cmp;
  }

  // Compare the children
  const term_ref* t1_child = term_begin(t1);
  const term_ref* t1_end = term_end(t1);
  const term_ref* t2_child = term_begin(t2);
  for (; t1_child != t1_end; ++ t1_child, ++ t2_child) {
    int child_cmp = cmp(*t1_child, *t2_child);
    if (child_cmp != 0) {
      return child_cmp;
    }
  }

  // Everything is equal
  return 0;
}

}
}
