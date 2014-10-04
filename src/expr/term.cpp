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
void term_ref::to_stream(std::ostream& out) const {
  const term_manager* tm = output::get_term_manager(out);
  if (tm == 0) {
    out << d_ref;
  } else {
    tm->get_term(*this).to_stream(out);
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

void term::to_stream_smt(std::ostream& out, const term_manager& tm) const {
  switch (d_op) {
  case OP_VARIABLE:
    out << "var";
    break;
  case OP_BOOL_CONSTANT:
    out << (tm.get_term_payload(this).get<bool>() ? "true" : "false");
    break;
  case OP_AND:
  case OP_OR:
  case OP_NOT:
  case OP_IMPLIES:
  case OP_XOR:
  case OP_ADD:
  case OP_SUB:
  case OP_MUL:
  case OP_DIV:
    out << "(" << get_smt_keyword(d_op);
    for (size_t i = 0; i < d_size; ++ i) {
      out << " " << d_children[i];
    }
    out << ")";
    break;
  case OP_REAL_CONSTANT:
    // Stream is already in SMT mode
    out << tm.get_term_extra(this).get<rational>();
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

}
}
