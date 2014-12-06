/*
 * btor_state.cpp
 *
 *  Created on: Dec 5, 2014
 *      Author: dejan
 */

#include "parser/btor/btor_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"

#include <cassert>

using namespace sal2;
using namespace parser;
using namespace expr;

using namespace std;

btor_state::btor_state(const system::context& context)
: d_context(context)
{
  // Add the basic types
  term_manager& tm = context.tm();
}

string btor_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

int btor_state::token_as_int(pANTLR3_COMMON_TOKEN token) {
  int value;
  std::stringstream ss;
  ss << token_text(token);
  ss >> value;
  return value;
}

integer btor_state::token_as_integer(pANTLR3_COMMON_TOKEN token, size_t base) {
  return integer(token_text(token), 10);
}

void btor_state::set_term(size_t index, term_ref term) {
  if (index >= d_terms.size()) {
    d_terms.resize(index + 1);
  }
  d_terms[index] = term;
}

expr::term_ref btor_state::get_term(int index) const {
  size_t i = index >= 0 ? index : -index;
  if (i >= d_terms.size() || d_terms[i].is_null()) {
    throw exception("Index not declared yet");
  }
  term_ref result = d_terms[i];
  if (index >= 0) {
    return result;
  } else {
    if (tm().type_of(result) == tm().boolean_type()) {
      return tm().mk_term(expr::TERM_NOT, result);
    } else {
      return tm().mk_term(expr::TERM_BV_NOT, result);
    }
  }
}

void btor_state::add_variable(size_t id, size_t size, std::string name) {
  term_ref type = tm().bitvector_type(size);
  term_ref term = tm().mk_variable(name, type);
  set_term(id, term);
  d_variables.push_back(id);
}

void btor_state::add_constant(size_t id, size_t size, const bitvector& bv) {
  term_ref term = tm().mk_bitvector_constant(bv);
  set_term(id, term);
}

static size_t power_log(size_t size) {
  assert(size > 0);
  size_t log = 0;
  while ((size & 1) == 0) {
    size >>= 1;
    log ++;
  }
  if (size != 1) {
    throw parser_exception("Bitvector size must be a power of two.");
  }
  return log;
}

void btor_state::add_term(size_t id, term_op op, size_t size, term_ref t1, term_ref t2) {
  if (size == 0) {
    throw parser_exception("Bitvector size must be non-negative");
  }
  term_ref term;
  switch (op) {
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR: {
    // Size is a power of two
    size_t size_log = power_log(size);
    // Padding
    bitvector bv(size - size_log);
    term_ref padding = tm().mk_bitvector_constant(bv);
    // Extend the shift factor to the size
    t2 = tm().mk_term(expr::TERM_BV_CONCAT, padding, t2);
    // Make the term
    term = tm().mk_term(op, t1, t2);
    break;
  }
  default:
    // Nothing to do
    term = tm().mk_term(op, t1, t2);
    break;
  }

  term_ref term_type = tm().type_of(term);
  if (term_type == tm().boolean_type()) {
    if (size != 1) {
      throw exception("Bitvector sizes don't match.");
    }
  } else if (tm().get_bitvector_type_size(term_type) != size) {
    throw exception("Bitvector sizes don't match.");
  }

  // Set the data
  set_term(id, term);
}

void btor_state::add_root(size_t id, size_t size, expr::term_ref t1) {
  d_roots.push_back(t1);
}
