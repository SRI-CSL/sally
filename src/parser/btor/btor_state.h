/*
 * btor_state.h
 *
 *  Created on: Dec 5, 2014
 *      Author: dejan
 */

#pragma once

#include <iosfwd>
#include <antlr3.h>

#include "system/context.h"

namespace sal2 {
namespace parser {

/** State attached to the parser */
class btor_state {

  /** The context */
  const system::context& d_context;

  // Map from indices to terms
  std::vector<expr::term_ref> d_terms;

  // List of variables indices
  std::vector<size_t> d_variables;

  // Map from variables to their next versions
  std::vector<size_t> d_next;

  // List of root nodes
  std::vector<expr::term_ref> d_roots;

  /** Set the term */
  void set_term(size_t index, expr::term_ref term);

public:

  /** Construct the parser state */
  btor_state(const system::context& context);

  /** Returns the term manager for the parser */
  expr::term_manager& tm() const { return d_context.tm(); }

  /** Returns the context for the parser */
  const system::context& ctx() const { return d_context; }

  /** Get the string of a token begin parsed */
  static
  std::string token_text(pANTLR3_COMMON_TOKEN token);

  /** Get the int value of a token begin parsed */
  static
  int token_as_int(pANTLR3_COMMON_TOKEN token);

  /** Get the integer value of a token begin parsed */
  static
  expr::integer token_as_integer(pANTLR3_COMMON_TOKEN token, size_t base);

  /** Get the term at index (negated if negative) */
  expr::term_ref get_term(int index) const;

  /** Add a variable */
  void add_variable(size_t id, size_t size, std::string name);

  /** Add a constant */
  void add_constant(size_t id, size_t size, const expr::bitvector& bv);

  /** Add a binary term */
  void add_term(size_t id, expr::term_op op, size_t size, expr::term_ref t1, expr::term_ref t2);

  /** Add a root node */
  void add_root(size_t id, size_t size, expr::term_ref t1);
};

}
}
