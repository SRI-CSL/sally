/*
 * term_ops.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/rational.h"
#include "utils/allocator.h"

namespace sal2 {
namespace expr {

/**
 * Enumeration of all term kinds. For each term kind, there is an associated
 * term_op_traits instantiation that defines the content of the specific kind
 * of term.
 */
enum term_op {

  // Types
  TYPE_BOOL,
  TYPE_INTEGER,
  TYPE_REAL,

  // Variables
  VARIABLE,

  // Equality
  TERM_EQ,

  // Boolean terms
  CONST_BOOL,
  TERM_AND,
  TERM_OR,
  TERM_NOT,
  TERM_IMPLIES,
  TERM_XOR,

  // Arithmetic terms
  CONST_RATIONAL,
  TERM_ADD,
  TERM_SUB,
  TERM_MUL,
  TERM_DIV,

  // Marker for the last
  OP_LAST
};

/**
 * The traits class contains an instantiation for each term kind. Any payload
 * types need to have an associated utils::hash specialization, copy constructors
 * and the operator ==.
 *
 * If the term has a payload it should define the payload_type to be of that
 * type, or otherwise define it to be alloc::empty_type.
 */
template <term_op op>
struct term_op_traits {
  /** Default terms have no payload, so we use the alloc::empty type. */
  typedef alloc::empty_type payload_type;
};

/**
 * Boolean constant terms have a payload of type bool and no children.
 */
template<>
struct term_op_traits<CONST_BOOL> {
  typedef bool payload_type;
};

/**
 * Rational constants terms have a payload of type rational (gmp) and no children.
 */
template<>
struct term_op_traits<CONST_RATIONAL> {
  typedef rational payload_type;
};

/**
 * Variables have a payload that is their name, and one child, which is the
 * name of the variable.
 */
template<>
struct term_op_traits<VARIABLE> {
  typedef std::string payload_type;
};

}
}
