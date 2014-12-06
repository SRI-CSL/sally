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
  d_one = tm().mk_bitvector_constant(bitvector(1, 1));
  d_zero = tm().mk_bitvector_constant(bitvector(1, 0));
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
  return integer(token_text(token), base);
}

void btor_state::set_term(size_t index, term_ref term, size_t size) {
  // Ensure size
  if (index >= d_terms.size()) {
    d_terms.resize(index + 1);
  }
  // Ensure bit-vector
  if (tm().type_of(term) == tm().boolean_type()) {
    term = tm().mk_term(expr::TERM_ITE, term, d_one, d_zero);
  }
  // Ensure the right size
  term_ref term_type = tm().type_of(term);
  if (tm().get_bitvector_type_size(term_type) != size) {
    throw exception("Bitvector sizes don't match.");
  }
  // Remember
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
  set_term(id, term, size);
  d_variables.push_back(id);
}

void btor_state::add_next_variable(size_t id, size_t size, size_t var_id, term_ref value) {
  var_to_var_map::const_iterator find = d_variables_next.find(var_id);
  if (find != d_variables_next.end()) {
    throw exception("Next already defined for this variable.");
  }
  if (tm().get_bitvector_type_size(tm().type_of(value)) != size) {
    throw exception("Bitvector sizes don't match");
  }
  d_variables_next[var_id] = id;
  set_term(id, value, size);
}

void btor_state::add_constant(size_t id, size_t size, const bitvector& bv) {
  term_ref term = tm().mk_bitvector_constant(bv);
  set_term(id, term, size);
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
    throw parser_exception("Bitvector size must be non-negative.");
  }

  term_ref term;

  switch (op) {
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR: {
    // Special treatment for shifts, size is a power of two
    size_t size_log = power_log(size);
    // Padding the shift amount to size
    bitvector bv(size - size_log);
    term_ref padding = tm().mk_bitvector_constant(bv);
    // Extend the shift factor to the size
    t2 = tm().mk_term(expr::TERM_BV_CONCAT, padding, t2);
    // Make the term
    term = tm().mk_term(op, t1, t2);
    break;
  }
  default:
    // Default, we just make it
    term = tm().mk_term(op, t1, t2);
  }

  // Set the data
  set_term(id, term, size);
}

void btor_state::add_ite(size_t id, size_t size, expr::term_ref c, expr::term_ref t_true, expr::term_ref t_false) {
  term_ref eq = tm().mk_term(expr::TERM_EQ, c, d_one);
  term_ref term = tm().mk_term(expr::TERM_ITE, eq, t_true, t_false);
  set_term(id, term, size);
}

void btor_state::add_slice(size_t id, size_t size, term_ref t, size_t high, size_t low) {
  term_ref term = tm().mk_bitvector_extract(t, bitvector_extract(high, low));
  set_term(id, term, size);
}

void btor_state::add_root(size_t id, size_t size, expr::term_ref term) {
  d_roots.push_back(term);
  set_term(id, term, size);
}
