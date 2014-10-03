/*
 * term.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include "expr/term.h"

#include <cstdlib>
#include <iomanip>
#include <cassert>

namespace sal2 {
namespace term {

static
void*& get_ostream_term_manager(std::ostream& out) {
  static const int xindex = std::ios_base::xalloc();
  return out.pword(xindex);
}

static
long& get_ostream_output_language(std::ostream& out) {
  static const int x_index = std::ios_base::xalloc();
  return out.iword(x_index);
}

void term_ref::to_stream(std::ostream& out) const {
  const term_manager* tm = static_cast<const term_manager*>(get_ostream_term_manager(out));
  if (tm == 0) {
    out << d_ref;
  } else {
    tm->get_term(*this).to_stream(out);
  }
}

void term::to_stream(std::ostream& out) const {
  output_language lang = static_cast<output_language>(get_ostream_output_language(out));
  const term_manager* tm = static_cast<const term_manager*>(get_ostream_term_manager(out));
  switch (lang) {
  case SMTLIB:
    to_stream_smt(out, *tm);
    break;
  default:
    assert(false);
  }
}

static inline
std::string get_smt_keyword(term_op op) {
  switch (op) {
  case OP_BOOL_AND:
    return "and";
  case OP_BOOL_OR:
    return "or";
  case OP_BOOL_NOT:
    return "not";
  case OP_BOOL_IMPLIES:
    return "implies";
  case OP_BOOL_XOR:
    return "xor";
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
    out << (get<bool>() ? "true" : "false");
    break;
  case OP_BOOL_AND:
  case OP_BOOL_OR:
  case OP_BOOL_NOT:
  case OP_BOOL_IMPLIES:
  case OP_BOOL_XOR:
    out << "(" << get_smt_keyword(d_op);
    for (size_t i = 0; i < d_size; ++ i) {
      out << " " << d_children[i];
    }
    out << ")";
    break;
  default:
    assert(false);
  }
}

static const size_t term_manager_intial_size = 10000;

term_manager::term_manager()
: d_memory(static_cast<char*>(std::malloc(term_manager_intial_size)))
, d_size(0)
, d_capacity(term_manager_intial_size)
{
}

std::ostream& operator << (std::ostream& out, const set_tm& stm) {
  get_ostream_term_manager(out) = (void*)stm.tm;
  return out;
}

term* term_manager::allocate(size_t size) {
  // Align the d_size
  size = (size + 7) & ~((size_t)7);

  // Make sure there is enough memory
  size_t requested = d_size + size;
  if (requested > d_capacity) {
    while (requested > d_capacity) {
      d_capacity += d_capacity / 2;
    }
    d_memory = (char*) std::realloc(d_memory, d_capacity);
  }

  // Actually allocate
  term* t = (term*)(d_memory + d_size);
  // Increase the d_size
  d_size  += size;
  // Return the clause memory
  return t;
}

term_ref term_manager::mk_term(term_op op, term_ref child) {
  size_t size = sizeof(term) + sizeof(term_ref);
  term* term = allocate(size);
  term->d_op = op;
  term->d_size = 1;
  term->d_children[0] = child;
  return get_ref(*term);
}

term_ref term_manager::mk_term(term_op op, term_ref child1, term_ref child2) {

  size_t size = sizeof(term) + 2*sizeof(term_ref);
  term* term = allocate(size);
  term->d_op = op;
  term->d_size = 2;
  term->d_children[0] = child1;
  term->d_children[1] = child2;
  return get_ref(*term);
}

term_ref term_manager::mk_term(term_op op, const std::vector<term_ref>& children) {
  size_t size = sizeof(term) + children.size() * sizeof(term_ref);
  term* term = allocate(size);
  term->d_op = op;
  term->d_size = children.size();
  for (size_t i = 0; i < children.size(); ++ i) {
    term->d_children[i] = children[i];
  }
  return get_ref(*term);
}

}
}
